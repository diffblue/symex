/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Concrete Symbolic Transformer

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string2int.h>

#ifdef DEBUG
#include <iostream>
#endif

#include "path_symex.h"
#include "path_symex_class.h"

bool path_symext::propagate(const exprt &src)
{
  // propagate things that are 'simple enough'
  if(src.is_constant())
    return true;
  else if(src.id()==ID_member)
    return propagate(to_member_expr(src).struct_op());
  else if(src.id()==ID_index)
    return false;
  else if(src.id()==ID_typecast)
    return propagate(to_typecast_expr(src).op());
  else if(src.id()==ID_symbol)
    return true;
  else if(src.id()==ID_address_of)
    return true;
  else if(src.id()==ID_plus)
  {
    forall_operands(it, src)
      if(!propagate(*it))
        return false;
    return true;
  }
  else if(src.id()==ID_array)
  {
    forall_operands(it, src)
      if(!propagate(*it))
        return false;
    return true;
  }
  else if(src.id()==ID_vector)
  {
    forall_operands(it, src)
      if(!propagate(*it))
        return false;
    return true;
  }
  else if(src.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(src);
    if(!propagate(if_expr.true_case()))
      return false;
    if(!propagate(if_expr.false_case()))
      return false;
    return true;
  }
  else if(src.id()==ID_array_of)
  {
    return propagate(to_array_of_expr(src).what());
  }
  else if(src.id()==ID_with)
  {
    // used by array theory
    return propagate(to_with_expr(src).old());
  }
  else if(src.id()==ID_union)
  {
    return propagate(to_union_expr(src).op());
  }
  else if(src.id()==ID_mult &&
          src.operands().size()==2 &&
          src.op0().find(ID_C_c_sizeof_type).is_not_nil())
  {
    return true;
  }
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract = to_byte_extract_expr(src);
    return propagate(byte_extract.op()) && propagate(byte_extract.offset());
  }
  else
  {
    return false;
  }
}

void path_symext::assign(
  path_symex_statet &state,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.id()==ID_side_effect) // catch side effects on rhs
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(rhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_allocate)
    {
      symex_allocate(state, lhs, side_effect_expr);
      return;
    }
    else if(statement==ID_java_new_array_data ||
            statement==ID_cpp_new ||
            statement==ID_cpp_new_array)
    {
      symex_new(state, lhs, side_effect_expr);
      return;
    }
    else if(statement==ID_nondet)
    {
      // done in statet:instantiate_rec
    }
    else if(statement==ID_va_start)
    {
      symex_va_start(state, lhs, side_effect_expr);
      return;
    }
    else
      throw errort() << "unexpected side-effect on rhs: " << statement;
  }
  else if(rhs.id()==ID_typecast &&
          to_typecast_expr(rhs).op().id()==ID_side_effect)
  {
    // cast + side effect: push to lhs
    auto new_lhs = typecast_exprt(lhs, rhs.type());
    auto new_rhs = to_typecast_expr(rhs).op();
    assign(state, new_lhs, new_rhs);
    return;
  }

  // The Java frontend generates nondet on the lhs
  if(lhs.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(lhs);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_nondet)
    {
      // ignore
      return;
    }
    else
      throw errort() << "unexpected side-effect on lhs: " << statement;
  }

  // read the address of the lhs, with propagation
  const exprt lhs_address=state.read(address_of_exprt(lhs));

  // get object we are assigning to
  const exprt dereferenced_lhs=
    lhs_address.id()==ID_address_of?
      to_address_of_expr(lhs_address).object():
      dereference_exprt(lhs_address);

  //const exprt dereferenced_lhs=dereference_exprt(lhs_address);

  // now SSA the lhs, no propagation
  const exprt ssa_lhs=state.read_no_propagate(dereferenced_lhs);

  // read the rhs
  const exprt ssa_rhs=state.read(rhs);

  // start recursion on ssa_lhs
  exprt::operandst _guard; // start with empty guard
  assign_rec(state, _guard, ssa_lhs, ssa_rhs);
}

void path_symext::symex_va_start(
  path_symex_statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw errort() << "va_start expected to have one operand";

  if(lhs.is_nil())
    return; // ignore

  if(state.threads[state.get_current_thread()].call_stack.empty())
    throw errort() << "va_start must be inside a function";

  // create an array that holds pointers to the ... parameters
  std::vector<exprt> va_args;
  const irep_idt function_id = state.function_id();
  const auto va_count =
    state.threads[state.get_current_thread()].call_stack.back().va_count;
  const auto element_type = pointer_type(void_type());

  for(std::size_t i=0; i<va_count; i++)
  {
    const irep_idt id=id2string(function_id)+"::va_arg"+std::to_string(i);
    const var_mapt::var_infot &var_info=state.config.var_map[id];
    const path_symex_statet::var_statet &var_state =
      state.get_var_state(var_info);
    const exprt symbol_expr=symbol_exprt(id, var_state.ssa_symbol.value().type());
    auto address = address_of_exprt(symbol_expr);
    auto casted = typecast_exprt::conditional_cast(address, element_type);
    va_args.push_back(casted);
  }

  // now build an array literal with those addresses
  auto array_type = array_typet(element_type, from_integer(va_count, size_type()));

  const irep_idt base_name = "va_args"+std::to_string(state.config.var_map.nondet_count);
  const irep_idt id="symex::"+id2string(base_name);
  state.config.var_map.nondet_count++;

  auxiliary_symbolt va_args_symbol;
  va_args_symbol.name=id;
  va_args_symbol.base_name=base_name;
  va_args_symbol.type=array_type;
  const auto symbol_expr = va_args_symbol.symbol_expr();
  state.config.var_map.new_symbols.add(std::move(va_args_symbol));

  // assign array to va_args symbol
  assign(state, symbol_expr, array_exprt(std::move(va_args), array_type));

  // now assign the address of that to the lhs
  exprt rhs =
    typecast_exprt::conditional_cast(
      address_of_exprt(symbol_expr, element_type),
      lhs.type());

  assign(state, lhs, rhs);
}

void path_symext::assign_rec_symbol(
  path_symex_statet &state,
  exprt::operandst &guard,
  const symbol_exprt &ssa_lhs,
  const exprt &ssa_rhs)
{
  if(has_prefix(id2string(ssa_lhs.get_identifier()),
                "symex::deref"))
    return; // ignore

  // These are expected to be SSA symbols
  assert(ssa_lhs.get_bool(ID_C_SSA_symbol));

  const irep_idt &full_identifier=ssa_lhs.get(ID_C_full_identifier);

  #ifdef DEBUG
  const irep_idt &ssa_identifier=expr.get_identifier();
  std::cout << "SSA symbol identifier: " << ssa_identifier << '\n';
  std::cout << "full identifier: " << full_identifier << '\n';
  #endif

  var_mapt::var_infot &var_info=state.config.var_map[full_identifier];
  assert(var_info.full_identifier==full_identifier);

  // increase the SSA counter and produce new SSA symbol expression
  var_info.increment_ssa_counter();
  symbol_exprt new_ssa_lhs=var_info.ssa_symbol();

  // ssa-ify the size
  if(var_mapt::is_unbounded_array(new_ssa_lhs.type()))
  {
    // disabled to preserve type consistency
    // exprt &size=to_array_type(new_ssa_lhs.type()).size();
    // size=state.read(size);
  }

  #ifdef DEBUG
  std::cout << "new_ssa_lhs: " << new_ssa_lhs.get_identifier() << '\n';
  #endif

  // record new state of lhs
  {
    // warning: reference var_state is not stable
    path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
    var_state.ssa_symbol=new_ssa_lhs;
  }

  // rhs nil means non-det assignment
  if(ssa_rhs.is_nil())
  {
    path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
    var_state.value={};
  }
  else
  {
    // consistency check
    if(!base_type_eq(ssa_rhs.type(), new_ssa_lhs.type(), state.config.ns))
    {
      #ifdef DEBUG
      std::cout << "ssa_rhs: " << ssa_rhs.pretty() << '\n';
      std::cout << "new_ssa_lhs: " << new_ssa_lhs.pretty() << '\n';
      #endif
      throw errort() << "assign_rec got different types";
    }

    // propagate the rhs?
    // warning: reference var_state is not stable
    path_symex_statet::var_statet &var_state=state.get_var_state(var_info);

    if(propagate(ssa_rhs))
      var_state.value=ssa_rhs;
    else
      var_state.value={};
  }

  // record the step
  state.record_step();
  stept &step=*state.history;

  step.ssa_guard=conjunction(guard);
  step.lhs=var_info.original;
  step.ssa_lhs=new_ssa_lhs;

  if(ssa_rhs.is_nil())
    // this is a tautology, added so the solver knows about the symbol
    step.ssa_rhs=new_ssa_lhs;
  else
    step.ssa_rhs=ssa_rhs;
}

void path_symext::assign_rec_member(
  path_symex_statet &state,
  exprt::operandst &guard,
  const member_exprt &ssa_lhs,
  const exprt &ssa_rhs)
{
  #ifdef DEBUG
  std::cout << "assign_rec ID_member\n";
  #endif

  const member_exprt &ssa_lhs_member_expr=to_member_expr(ssa_lhs);
  const exprt &struct_op=ssa_lhs_member_expr.struct_op();

  const typet &compound_type=
    state.config.ns.follow(struct_op.type());

  if(compound_type.id()==ID_struct)
  {
    // We flatten the top-level structs, so this one is inside an
    // array or a union.

    exprt member_name(ID_member_name);
    member_name.set(
      ID_component_name,
      ssa_lhs_member_expr.get_component_name());

    with_exprt new_rhs(struct_op, member_name, ssa_rhs);

    assign_rec(state, guard, struct_op, new_rhs);
  }
  else if(compound_type.id()==ID_union)
  {
    // rewrite into byte_extract, and do again
    exprt offset=from_integer(0, index_type());

    byte_extract_exprt
      new_ssa_lhs(byte_update_id(), struct_op, offset, ssa_rhs.type());

    assign_rec(state, guard, new_ssa_lhs, ssa_rhs);
  }
  else
    throw errort() << "assign_rec: member expects struct or union type";
}

void path_symext::assign_rec_index(
  path_symex_statet &state,
  exprt::operandst &guard,
  const index_exprt &ssa_lhs,
  const exprt &ssa_rhs)
{
  #ifdef DEBUG
  std::cout << "assign_rec ID_index\n";
  #endif

  const auto &index_expr=to_index_expr(ssa_lhs);

  // This must be an unbounded array.
  if(!var_mapt::is_unbounded_array(index_expr.array().type()))
    throw errort() << "unexpected array index on lhs";

  const exprt new_ssa_lhs=index_expr.array();

  // can now constant-propagate the array in the RHS
  assert(new_ssa_lhs.get_bool(ID_C_SSA_symbol));
  const exprt new_array_rhs = 
    state.read(symbol_exprt(new_ssa_lhs.get(ID_C_full_identifier), new_ssa_lhs.type()));

  const exprt new_ssa_rhs=with_exprt(new_array_rhs, index_expr.index(), ssa_rhs);

  assign_rec(state, guard, new_ssa_lhs, new_ssa_rhs);
}

void path_symext::assign_rec(
  path_symex_statet &state,
  exprt::operandst &guard,
  const exprt &ssa_lhs,
  const exprt &ssa_rhs)
{
  // const typet &ssa_lhs_type=state.config.ns.follow(ssa_lhs.type());

  #ifdef DEBUG
  std::cout << "assign_rec: " << ssa_lhs.pretty() << '\n';
  // std::cout << "ssa_lhs_type: " << ssa_lhs_type.id() << '\n';
  #endif

  if(ssa_lhs.id()==ID_symbol)
  {
    assign_rec_symbol(state, guard, to_symbol_expr(ssa_lhs), ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_typecast)
  {
    // dereferencing might yield a typecast
    const exprt &new_ssa_lhs=to_typecast_expr(ssa_lhs).op();
    typecast_exprt new_rhs(ssa_rhs, new_ssa_lhs.type());

    assign_rec(state, guard, new_ssa_lhs, new_rhs);
  }
  else if(ssa_lhs.id()==ID_member)
  {
    assign_rec_member(state, guard, to_member_expr(ssa_lhs), ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_index)
  {
    assign_rec_index(state, guard, to_index_expr(ssa_lhs), ssa_rhs);
  }
  else if(ssa_lhs.id()==ID_dereference)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_dereference\n";
    #endif

    //throw "unexpected dereference on lhs";
    // ignore
  }
  else if(ssa_lhs.id()==ID_if)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_if\n";
    #endif

    const if_exprt &lhs_if_expr=to_if_expr(ssa_lhs);
    exprt cond=lhs_if_expr.cond();

    // true
    guard.push_back(cond);
    assign_rec(state, guard, lhs_if_expr.true_case(), ssa_rhs);
    guard.pop_back();

    // false
    guard.push_back(not_exprt(cond));
    assign_rec(state, guard, lhs_if_expr.false_case(), ssa_rhs);
    guard.pop_back();
  }
  else if(ssa_lhs.id()==ID_byte_extract_little_endian ||
          ssa_lhs.id()==ID_byte_extract_big_endian)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_byte_extract\n";
    #endif

    const byte_extract_exprt &byte_extract_expr=
      to_byte_extract_expr(ssa_lhs);

    // assignment to byte_extract operators:
    // turn into byte_update operator

    irep_idt new_id;

    if(ssa_lhs.id()==ID_byte_extract_little_endian)
      new_id=ID_byte_update_little_endian;
    else if(ssa_lhs.id()==ID_byte_extract_big_endian)
      new_id=ID_byte_update_big_endian;
    else
      UNREACHABLE;

    byte_update_exprt new_rhs(
      new_id, byte_extract_expr.op(), byte_extract_expr.offset(), ssa_rhs);

    const exprt new_ssa_lhs=byte_extract_expr.op();

    assign_rec(state, guard, new_ssa_lhs, new_rhs);
  }
  else if(ssa_lhs.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(state.config.ns.follow(ssa_lhs.type()));
    const struct_typet::componentst &components=
      struct_type.components();

    // split up into components
    const exprt::operandst &operands=ssa_lhs.operands();

    assert(operands.size()==components.size());

    for(std::size_t i=0; i<components.size(); i++)
    {
      exprt new_rhs;

      if(ssa_rhs.is_nil())
        new_rhs=nil_exprt();
      else if(ssa_rhs.id()==ID_struct &&
              ssa_rhs.operands().size()==components.size())
        new_rhs=ssa_rhs.operands()[i];
      else
      {
        new_rhs=simplify_expr(
            member_exprt(
              ssa_rhs,
              components[i].get_name(),
              components[i].type()),
            state.config.ns);
      }

      assign_rec(state, guard, operands[i], new_rhs);
    }
  }
  else if(ssa_lhs.id()==ID_array)
  {
    const typet &ssa_lhs_type=state.config.ns.follow(ssa_lhs.type());

    if(ssa_lhs_type.id()!=ID_array)
      throw errort() << "array constructor must have array type";

    const array_typet &array_type=
      to_array_type(ssa_lhs_type);

    const exprt::operandst &operands=ssa_lhs.operands();

    // split up into elements
    if(ssa_rhs.id()==ID_array &&
       ssa_rhs.operands().size()==operands.size())
    {
      exprt::operandst::const_iterator lhs_it=operands.begin();
      forall_operands(it, ssa_rhs)
      {
        assign_rec(state, guard, *lhs_it, *it);
        ++lhs_it;
      }
    }
    else
    {
      for(std::size_t i=0; i<operands.size(); i++)
      {
        exprt new_rhs=
          ssa_rhs.is_nil()?ssa_rhs:
          simplify_expr(
            index_exprt(
              ssa_rhs,
              from_integer(i, index_type()),
              array_type.subtype()),
            state.config.ns);
        assign_rec(state, guard, operands[i], new_rhs);
      }
    }
  }
  else if(ssa_lhs.id()==ID_string_constant ||
          ssa_lhs.id()=="NULL-object" ||
          ssa_lhs.id()=="zero_string" ||
          ssa_lhs.id()=="is_zero_string" ||
          ssa_lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else
  {
    // ignore
    throw errort()
      << "path_symext::assign_rec(): unexpected lhs: " << ssa_lhs.id();
  }
}

void path_symext::function_call_symbol(
  path_symex_statet &state,
  const code_function_callt &call,
  const symbol_exprt &function,
  std::list<path_symex_statet> &further_states)
{
  const irep_idt &function_identifier=
    function.get_identifier();

  // find the function
  auto f_it = state.config.get_function(function_identifier);
  const auto &function_entry = f_it->second;

  // turn the arguments into SSA
  exprt::operandst ssa_arguments=call.arguments();
  for(auto &arg : ssa_arguments)
    arg=state.read(arg);

  // Fix types of the arguments, if needed
  {
    const code_typet::parameterst &parameters=
      to_code_type(function.type()).parameters();

    for(std::size_t i=0; i<ssa_arguments.size(); i++)
      if(i<parameters.size())
      {
        ssa_arguments[i]=typecast_exprt::conditional_cast(
          ssa_arguments[i], parameters[i].type());
      }
  }

  // record the function we call and the arguments
  state.history->called_function=function_identifier;
  state.history->function_arguments.resize(ssa_arguments.size());

  for(std::size_t i=0; i<ssa_arguments.size(); i++)
  {
    // store rhs
    state.history->function_arguments[i].ssa_rhs=ssa_arguments[i];

    // assign an lhs for every argument
    if(ssa_arguments[i].id()==ID_symbol)
      state.history->function_arguments[i].ssa_lhs=to_symbol_expr(ssa_arguments[i]);
    else
    {
      irep_idt id="symex_arg::"+id2string(function_identifier)+"::"+std::to_string(i);
      symbol_exprt arg_symbol(id, ssa_arguments[i].type());
      auto &var_info=state.config.var_map(id, irep_idt(), arg_symbol);
      state.history->function_arguments[i].ssa_lhs=var_info.ssa_symbol();
      var_info.increment_ssa_counter();
    }
  }

  // do we have a body?
  if(!function_entry.body_available())
  {
    // no body
    state.config.no_body(function_identifier);

    // this is a skip
    if(call.lhs().is_not_nil())
      assign(state, call.lhs(), nil_exprt());

    state.next_pc();
    return;
  }

  // push a frame on the call stack
  path_symex_statet::threadt &thread=
    state.threads[state.get_current_thread()];
  thread.call_stack.push_back(path_symex_statet::framet());
  auto &frame = thread.call_stack.back();
  frame.current_function=function_identifier;
  frame.return_location=thread.pc.next_loc();
  frame.return_lhs=call.lhs();
  frame.return_rhs={};
  frame.hidden_function=function_entry.is_hidden();
  frame.va_count = 0; // set below

  #if 0
  for(loc_reft l=function_entry_point; ; ++l)
  {
    if(locs[l].target->is_end_function())
      break;
    if(locs[l].target->is_decl())
    {
      // make sure we have the local in the var_map
      state.
    }
  }

  // save the locals into the frame
  for(locst::local_variablest::const_iterator
      it=function_entry.local_variables.begin();
      it!=function_entry.local_variables.end();
      it++)
  {
    unsigned nr=state.config.var_map[*it].number;
    thread.call_stack.back().saved_local_vars[nr]=thread.local_vars[nr];
  }
  #endif

  const code_typet &code_type=function_entry.type;
  const code_typet::parameterst &function_parameters=code_type.parameters();

  // keep track when va arguments begin.
  std::size_t va_args_start_index=0;

  // now assign the argument values to parameters
  for(std::size_t i=0; i<ssa_arguments.size(); i++)
  {
    if(function_parameters.size()!=f_it->second.parameter_identifiers.size())
      throw errort() << "function " << function_identifier
        << " has wrong number of parameter identifiers";

    if(i<function_parameters.size())
    {
      const code_typet::parametert &function_parameter=function_parameters[i];
      irep_idt identifier=f_it->second.parameter_identifiers[i];

      if(identifier.empty())
        throw errort() << "function_call " << function_identifier
          << " no identifier for function parameter";

      symbol_exprt lhs(identifier, function_parameter.type());

      const exprt ssa_rhs=ssa_arguments[i];
      const exprt ssa_lhs=state.read_no_propagate(lhs);
      assert(ssa_rhs.type()==ssa_lhs.type());

      exprt::operandst _guard; // start with empty guard
      assign_rec(state, _guard, ssa_lhs, ssa_rhs);
    }
    else if(va_args_start_index==0)
      va_args_start_index=i;
  }

  if(code_type.has_ellipsis())
  {
    std::size_t va_count=0;

    for(std::size_t i=va_args_start_index; i<ssa_arguments.size(); i++)
    {
      const exprt ssa_rhs=ssa_arguments[i];

      irep_idt id=id2string(function_identifier)+"::va_arg"
          +std::to_string(va_count);

      // clear the var_state, since the type may have changed
      const symbol_exprt symbol_expr(id, ssa_rhs.type());
      auto &var_info=state.config.var_map(id, irep_idt(), symbol_expr);
      var_info.original=symbol_expr;
      state.get_var_state(var_info).ssa_symbol = {};

      va_count++;

      const symbol_exprt lhs=symbol_expr;

      // ssa the lhs
      const exprt ssa_lhs=
        state.read_no_propagate(lhs);

      assert(lhs.type()==ssa_rhs.type());
      exprt::operandst _guard; // start with empty guard
      assign_rec(state, _guard, ssa_lhs, ssa_rhs);
    }

    thread.call_stack.back().va_count = va_count;
  }

  // update statistics
  state.recursion_map[function_identifier]++;

  // set the new PC
  assert(!function_entry.body.instructions.empty());
  thread.pc=
    loc_reft(function_identifier, function_entry.body.instructions.begin());
}

void path_symext::function_call(
  path_symex_statet &state,
  const code_function_callt &call,
  std::list<path_symex_statet> &further_states)
{
  exprt f=state.read(call.function());
  function_call_rec(state, call, f, further_states);
}

void path_symext::function_call_rec(
  path_symex_statet &state,
  const code_function_callt &call,
  const exprt &function,
  std::list<path_symex_statet> &further_states)
{
  #ifdef DEBUG
  std::cout << "function_call_rec: " << function.pretty() << '\n';
  #endif

  if(function.id()==ID_symbol)
  {
    function_call_symbol(state, call, to_symbol_expr(function), further_states);
  }
  else if(function.id()==ID_dereference)
  {
    // should not happen, we read() before
    throw errort() << "function_call_rec got dereference";
  }
  else if(function.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(function);
    exprt ssa_guard=if_expr.cond();

    // add a 'further state' for the false-case

    {
      further_states.push_back(state);
      path_symex_statet &false_state=further_states.back();
      false_state.record_step();
      false_state.history->ssa_guard=not_exprt(ssa_guard);
      function_call_rec(
        further_states.back(), call, if_expr.false_case(), further_states);
    }

    // do the true-case in 'state'
    {
      state.record_step();
      state.history->ssa_guard=ssa_guard;
      function_call_rec(state, call, if_expr.true_case(), further_states);
    }
  }
  else if(function.id()==ID_typecast)
  {
    // ignore
    function_call_rec(
      state, call, to_typecast_expr(function).op(), further_states);
  }
  else if(function.id()=="dereference_failure")
  {
    // give up
    throw errort()
      << "function_call_rec got dereference_failure at "
      << state.pc();
  }
  else
  {
    throw errort()
      << "TODO: function_call " << function.id()
      << " at " << state.pc();
  }
}

void path_symext::return_from_function(path_symex_statet &state)
{
  path_symex_statet::threadt &thread=state.threads[state.get_current_thread()];

  // returning from very last function?
  if(thread.call_stack.empty())
  {
    state.disable_current_thread();

    // main thread?
    if(state.get_current_thread()==0)
      state.make_terminated();
  }
  else
  {
    // update statistics
    state.recursion_map[thread.call_stack.back().current_function]--;

    // set PC to return location
    thread.pc=thread.call_stack.back().return_location;

    // assign the return value
    if(thread.call_stack.back().return_rhs.has_value() &&
       thread.call_stack.back().return_lhs.has_value())
    {
      assign(state, thread.call_stack.back().return_lhs.value(),
                    thread.call_stack.back().return_rhs.value());
    }

    // restore the local variables
    for(path_symex_statet::var_state_mapt::const_iterator
        it=thread.call_stack.back().saved_local_vars.begin();
        it!=thread.call_stack.back().saved_local_vars.end();
        it++)
    {
      thread.local_vars[it->first]=it->second;
    }

    // kill the frame
    thread.call_stack.pop_back();
  }
}

void path_symext::set_return_value(
  path_symex_statet &state,
  const exprt &v)
{
  path_symex_statet::threadt &thread=
    state.threads[state.get_current_thread()];

  // returning from very last function?
  if(!thread.call_stack.empty())
    thread.call_stack.back().return_rhs=v;
}

void path_symext::do_goto(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  PRECONDITION(instruction.is_goto());

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  exprt ssa_guard=state.read(instruction.get_condition());

  if(ssa_guard.is_true()) // branch taken always
  {
    state.record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    state.set_pc(state.pc().get_target());
    return; // we are done
  }

  if(!ssa_guard.is_false())
  {
    // branch taken case
    // copy the state into 'further_states'
    further_states.push_back(state);
    further_states.back().record_step();
    further_states.back().history->branch=stept::BRANCH_TAKEN;
    further_states.back().set_pc(state.pc().get_target());
    further_states.back().history->ssa_guard=ssa_guard;
  }

  // branch not taken case
  exprt negated_ssa_guard=not_exprt(ssa_guard);
  state.record_step();
  state.history->branch=stept::BRANCH_NOT_TAKEN;
  state.next_pc();
  state.history->ssa_guard=negated_ssa_guard;
}

void path_symext::do_goto(
  path_symex_statet &state,
  bool taken)
{
  state.record_step();

  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  exprt ssa_guard=state.read(instruction.get_condition());

  if(taken)
  {
    // branch taken case
    state.set_pc(state.pc().get_target());
    state.history->ssa_guard=ssa_guard;
    state.history->branch=stept::BRANCH_TAKEN;
  }
  else
  {
    // branch not taken case
    exprt negated_ssa_guard=not_exprt(ssa_guard);
    state.next_pc();
    state.history->ssa_guard=negated_ssa_guard;
    state.history->branch=stept::BRANCH_NOT_TAKEN;
  }
}

void path_symext::operator()(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  #ifdef DEBUG
  std::cout << "path_symext::operator(): "
            << state.pc() << " "
            << instruction.type
            << '\n';
  #endif

  // update some statistics
  state.increase_depth();

  switch(instruction.type)
  {
  case END_FUNCTION:
    // pop the call stack
    state.record_step();
    return_from_function(state);
    break;

  case RETURN:
    // sets the return value, but doesn't actually return
    state.record_step();
    state.next_pc();

    if(instruction.get_return().operands().size()==1)
      set_return_value(state, instruction.code.op0());

    break;

  case START_THREAD:
    {
      auto target = state.pc().get_target();

      state.record_step();
      state.next_pc();

      // ordering of the following matters due to vector instability
      path_symex_statet::threadt &new_thread=state.add_thread();
      path_symex_statet::threadt &old_thread=
        state.threads[state.get_current_thread()];
      new_thread.pc=target;
      new_thread.local_vars=old_thread.local_vars;
    }
    break;

  case END_THREAD:
    state.record_step();
    state.disable_current_thread();
    break;

  case GOTO:
    state.increase_no_branches();
    do_goto(state, further_states);
    break;

  case CATCH:
    // ignore for now
    state.record_step();
    state.next_pc();
    break;

  case THROW:
    state.record_step();
    throw errort()
      << "THROW not yet implemented"; // NOLINT(readability/throw)

  case ASSUME:
    state.record_step();
    state.next_pc();
    if(instruction.get_condition().is_false())
      state.make_infeasible();
    else
    {
      exprt ssa_guard=state.read(instruction.get_condition());
      state.history->ssa_guard=ssa_guard;
    }
    break;

  case ASSERT:
  case SKIP:
  case LOCATION:
    state.record_step();
    state.next_pc();
    break;

  case DEAD:
    // assigning an RHS of NIL means 'nondet'
    assign(state, instruction.get_dead().symbol(), nil_exprt());
    state.next_pc();
    break;

  case DECL:
    // assigning an RHS of NIL means 'nondet'
    assign(state, instruction.get_decl().symbol(), nil_exprt());
    state.next_pc();
    break;

  case ATOMIC_BEGIN:
    if(state.inside_atomic_section)
      throw errort() << "nested ATOMIC_BEGIN";

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=true;
    break;

  case ATOMIC_END:
    if(!state.inside_atomic_section)
      throw errort() << "ATOMIC_END unmatched"; // NOLINT(readability/throw)

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=false;
    break;

  case ASSIGN:
    assign(state, instruction.get_assign());
    state.next_pc();
    break;

  case FUNCTION_CALL:
    state.record_step();
    function_call(
      state, instruction.get_function_call(), further_states);
    break;

  case OTHER:
    state.record_step();

    {
      const codet &code=instruction.code;
      const irep_idt &statement=code.get_statement();

      if(statement==ID_array_set)
      {
        if(code.operands().size()!=2)
          throw errort() << "array_set expects two operands";

        // read the address of the lhs, with propagation
        const exprt lhs=state.read(code.op0());

        // must be address_of index of array symbol
        if(lhs.id()!=ID_address_of ||
           lhs.operands().size()!=1)
          throw errort() << "array_set expects address";

        if(lhs.op0().id()!=ID_index ||
           lhs.op0().operands().size()!=2)
          throw errort() << "array_set expects address_of index";

        const exprt &array=lhs.op0().op0();

        if(array.id()!=ID_symbol)
          throw errort() << "array_set expects address_of of index of symbol";

        const auto &array_type=to_array_type(array.type());

        const exprt rhs=array_of_exprt(code.op1(), array_type);

        assign(state, array, rhs);
      }
      else if(statement==ID_expression)
      {
        // like SKIP
      }
      else if(statement==ID_printf)
      {
        // ignore for now (should record stuff printed)
      }
      else if(statement==ID_asm)
      {
        // ignore for now
      }
      else if(statement==ID_fence)
      {
        // ignore for SC
      }
      else if(statement==ID_havoc_object)
      {
        DATA_INVARIANT(code.operands().size()==1,
          "havoc_object must have one operand");
        DATA_INVARIANT(code.op0().type().id()==ID_pointer,
          "havoc_object gets pointer operand");

        // get object we are assigning to
        const exprt dereferenced_lhs=
          dereference_exprt(code.op0());

        const exprt ssa_lhs=
          state.read_no_propagate(dereferenced_lhs);

        const exprt ssa_rhs=
          nil_exprt();

        exprt::operandst _guard;
        assign_rec(state, _guard, ssa_lhs, ssa_rhs);
      }
      else if(statement==ID_input)
      {
        // just needs to be recorded
      }
      else if(statement==ID_output)
      {
        // just needs to be recorded
      }
      else
        throw errort() << "unexpected OTHER statement: " << statement;
    }

    state.next_pc();
    break;

  case NO_INSTRUCTION_TYPE:
    throw errort() << "path_symext: got 'no instruction type'";

  case INCOMPLETE_GOTO:
    throw errort() << "path_symext: got 'incomplete goto'";

  default:
    throw errort() << "path_symext: unexpected instruction";
  }
}

void path_symext::operator()(path_symex_statet &state)
{
  std::list<path_symex_statet> further_states;
  operator()(state, further_states);
  if(!further_states.empty())
    throw errort() << "path_symext got unexpected further states";
}

void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states)
{
  path_symext path_symex;
  path_symex(state, further_states);
}

void path_symex(path_symex_statet &state)
{
  path_symext path_symex;
  path_symex(state);
}

void path_symex_goto(
  path_symex_statet &state,
  bool taken)
{
  path_symext path_symex;
  path_symex.do_goto(state, taken);
}

void path_symex_assert_fail(path_symex_statet &state)
{
  path_symext path_symex;
  path_symex.do_assert_fail(state);
}
