/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Concrete Symbolic Transformer

#include "path_symex.h"

#include <util/arith_tools.h>
#include <util/expr_initializer.h>
#include <util/simplify_expr.h>
#include <util/string2int.h>
#include <util/byte_operators.h>
#include <util/pointer_offset_size.h>
#include <util/base_type.h>
#include <util/prefix.h>
#include <util/c_types.h>

#include <pointer-analysis/dereference.h>

#include "path_symex_class.h"

#ifdef DEBUG
#include <iostream>
#endif

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
  else if(src.id()==ID_union)
  {
    return propagate(to_union_expr(src).op());
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
    else if(statement==ID_gcc_builtin_va_arg_next)
    {
      symex_va_arg_next(state, lhs, side_effect_expr);
      return;
    }
    else
      throw "unexpected side-effect on rhs: "+id2string(statement);
  }

  // read the address of the lhs, with propagation
  const exprt lhs_address=state.read(address_of_exprt(lhs));

  // get object we are assigning to
  const exprt dereferenced_lhs=
    lhs_address.id()==ID_address_of?
      to_address_of_expr(lhs_address).object():
      dereference_exprt(lhs_address);

  // now SSA the lhs, no propagation
  const exprt ssa_lhs=
    state.read_no_propagate(dereferenced_lhs);

  // read the rhs
  const exprt ssa_rhs=state.read(rhs);

  // start recursion on ssa_lhs
  exprt::operandst _guard; // start with empty guard
  assign_rec(state, _guard, dereferenced_lhs, ssa_lhs, ssa_rhs);
}

static irep_idt get_old_va_symbol(
  const path_symex_statet &state,
  const exprt &src)
{
  if(src.id()==ID_typecast)
    return get_old_va_symbol(state, to_typecast_expr(src).op());
  else if(src.id()==ID_address_of)
  {
    const exprt &op=to_address_of_expr(src).object();

    if(op.id()==ID_symbol)
      return to_symbol_expr(op).get_identifier();
  }

  return irep_idt();
}

void path_symext::symex_va_arg_next(
  path_symex_statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw "va_arg_next expected to have one operand";

  if(lhs.is_nil())
    return; // ignore

  exprt tmp=state.read(code.op0()); // constant prop on va_arg parameter

  // Get old symbol of va_arg and modify it to generate a new one.
  irep_idt id=get_old_va_symbol(state, tmp);
  exprt rhs=
    zero_initializer(
      lhs.type(),
      code.source_location(),
      state.var_map.ns);

  if(!id.empty())
  {
    // strip last name off id to get function name
    std::size_t pos=id2string(id).rfind("::");
    if(pos!=std::string::npos)
    {
      irep_idt function_identifier=std::string(id2string(id), 0, pos);
      std::string base=id2string(function_identifier)+"::va_arg";

      /*
       * Construct the identifier of the va_arg argument such that it
       * corresponds to the respective one set upon function call
       */
      if(has_prefix(id2string(id), base))
        id=base
            +std::to_string(
                safe_string2unsigned(
                    std::string(id2string(id), base.size(), std::string::npos))
                    +1);
      else
        id=base+"0";

      const var_mapt::var_infot &var_info=state.var_map[id];

      if(var_info.full_identifier==id)
      {
        const path_symex_statet::var_statet &var_state
          =state.get_var_state(var_info);
        const exprt symbol_expr=symbol_exprt(id, var_state.ssa_symbol.type());
        rhs=address_of_exprt(symbol_expr);
        rhs.make_typecast(lhs.type());
      }
    }
  }

  assign(state, lhs, rhs);
}

void path_symext::assign_rec(
  path_symex_statet &state,
  exprt::operandst &guard,
  const exprt &dereferenced_lhs,
  const exprt &ssa_lhs,
  const exprt &ssa_rhs)
{
  // const typet &ssa_lhs_type=state.var_map.ns.follow(ssa_lhs.type());

  #ifdef DEBUG
  std::cout << "assign_rec: " << ssa_lhs.pretty() << '\n';
  // std::cout << "ssa_lhs_type: " << ssa_lhs_type.id() << '\n';
  #endif

  if(ssa_lhs.id()==ID_symbol)
  {
    if(has_prefix(id2string(to_symbol_expr(ssa_lhs).get_identifier()),
                  "symex::deref"))
      return; // ignore

    // These are expected to be SSA symbols
    assert(ssa_lhs.get_bool(ID_C_SSA_symbol));

    const symbol_exprt &symbol_expr=to_symbol_expr(ssa_lhs);
    const irep_idt &full_identifier=symbol_expr.get(ID_C_full_identifier);

    #ifdef DEBUG
    const irep_idt &ssa_identifier=symbol_expr.get_identifier();
    std::cout << "SSA symbol identifier: " << ssa_identifier << '\n';
    std::cout << "full identifier: " << full_identifier << '\n';
    #endif

    var_mapt::var_infot &var_info=state.var_map[full_identifier];
    assert(var_info.full_identifier==full_identifier);

    // increase the SSA counter and produce new SSA symbol expression
    var_info.increment_ssa_counter();
    symbol_exprt new_ssa_lhs=var_info.ssa_symbol();

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
      var_state.value=nil_exprt();
    }
    else
    {
      // consistency check
      if(!base_type_eq(ssa_rhs.type(), new_ssa_lhs.type(), state.var_map.ns))
      {
        #ifdef DEBUG
        std::cout << "ssa_rhs: " << ssa_rhs.pretty() << '\n';
        std::cout << "new_ssa_lhs: " << new_ssa_lhs.pretty() << '\n';
        #endif
        throw "assign_rec got different types";
      }

      // propagate the rhs?
      // warning: reference var_state is not stable
      path_symex_statet::var_statet &var_state=state.get_var_state(var_info);
      var_state.value=propagate(ssa_rhs)?ssa_rhs:nil_exprt();
    }

    // record the step
    state.record_step();
    stept &step=*state.history;

    step.ssa_guard=conjunction(guard);
    step.lhs=dereferenced_lhs;
    step.ssa_lhs=new_ssa_lhs;

    if(ssa_rhs.is_nil())
      // this is a tautology, added so the solver knows about the symbol
      step.ssa_rhs=new_ssa_lhs;
    else
      step.ssa_rhs=ssa_rhs;
  }
  else if(ssa_lhs.id()==ID_typecast)
  {
    // dereferencing might yield a typecast
    const exprt &new_ssa_lhs=to_typecast_expr(ssa_lhs).op();
    typecast_exprt new_rhs(ssa_rhs, new_ssa_lhs.type());

    assign_rec(state, guard, dereferenced_lhs, new_ssa_lhs, new_rhs);
  }
  else if(ssa_lhs.id()==ID_member)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_member\n";
    #endif

    const member_exprt &ssa_lhs_member_expr=to_member_expr(ssa_lhs);
    const exprt &struct_op=ssa_lhs_member_expr.struct_op();

    const typet &compound_type=
      state.var_map.ns.follow(struct_op.type());

    if(compound_type.id()==ID_struct)
    {
      // We flatten the top-level structs, so this one is inside an
      // array or a union.

      exprt member_name(ID_member_name);
      member_name.set(
        ID_component_name,
        ssa_lhs_member_expr.get_component_name());

      with_exprt new_rhs(struct_op, member_name, ssa_rhs);

      assign_rec(state, guard, dereferenced_lhs, struct_op, new_rhs);
    }
    else if(compound_type.id()==ID_union)
    {
      // rewrite into byte_extract, and do again
      exprt offset=from_integer(0, index_type());

      byte_extract_exprt
        new_ssa_lhs(byte_update_id(), struct_op, offset, ssa_rhs.type());

      assign_rec(state, guard, dereferenced_lhs, new_ssa_lhs, ssa_rhs);
    }
    else
      throw "assign_rec: member expects struct or union type";
  }
  else if(ssa_lhs.id()==ID_index)
  {
    #ifdef DEBUG
    std::cout << "assign_rec ID_index\n";
    #endif

    throw "unexpected array index on lhs";
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
    assign_rec(state, guard, dereferenced_lhs, lhs_if_expr.true_case(), ssa_rhs);
    guard.pop_back();

    // false
    guard.push_back(not_exprt(cond));
    assign_rec(state, guard, dereferenced_lhs, lhs_if_expr.false_case(), ssa_rhs);
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

    byte_update_exprt new_rhs(new_id);

    new_rhs.type()=byte_extract_expr.op().type();
    new_rhs.op()=byte_extract_expr.op();
    new_rhs.offset()=byte_extract_expr.offset();
    new_rhs.value()=ssa_rhs;

    const exprt new_ssa_lhs=byte_extract_expr.op();

    assign_rec(state, guard, dereferenced_lhs, new_ssa_lhs, new_rhs);
  }
  else if(ssa_lhs.id()==ID_struct)
  {
    const struct_typet &struct_type=
      to_struct_type(state.var_map.ns.follow(ssa_lhs.type()));
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
            state.var_map.ns);
      }

      member_exprt new_dereferenced_lhs(
        dereferenced_lhs, components[i].get_name(), components[i].type());

      assign_rec(state, guard, new_dereferenced_lhs, operands[i], new_rhs);
    }
  }
  else if(ssa_lhs.id()==ID_array)
  {
    const typet &ssa_lhs_type=state.var_map.ns.follow(ssa_lhs.type());

    if(ssa_lhs_type.id()!=ID_array)
      throw "array constructor must have array type";

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
        assign_rec(state, guard, dereferenced_lhs, *lhs_it, *it);
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
            state.var_map.ns);
        assign_rec(state, guard, dereferenced_lhs, operands[i], new_rhs);
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
    throw "path_symext::assign_rec(): unexpected lhs: "+ssa_lhs.id_string();
  }
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
    const irep_idt &function_identifier=
      to_symbol_expr(function).get_identifier();

    // find the function
    locst::function_mapt::const_iterator f_it=
      state.locs.function_map.find(function_identifier);

    if(f_it==state.locs.function_map.end())
      throw
        "failed to find `"+id2string(function_identifier)+"' in function_map";

    // record the function we call
    state.history->function_identifier=function_identifier;

    const locst::function_entryt &function_entry=f_it->second;

    loc_reft function_entry_point=function_entry.first_loc;

    // do we have a body?
    if(function_entry_point==loc_reft())
    {
      // no body
      //warning() << "**** WARNING: no body for function "
      //          << function_identifier << eom;

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
    thread.call_stack.back().current_function=function_identifier;
    thread.call_stack.back().return_location=thread.pc.next_loc();
    thread.call_stack.back().return_lhs=call.lhs();
    thread.call_stack.back().return_rhs=nil_exprt();
    thread.call_stack.back().hidden_function=function_entry.hidden;

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
      unsigned nr=state.var_map[*it].number;
      thread.call_stack.back().saved_local_vars[nr]=thread.local_vars[nr];
    }
    #endif

    const code_typet &code_type=function_entry.type;

    const code_typet::parameterst &function_parameters=code_type.parameters();

    const exprt::operandst &call_arguments=call.arguments();

    // keep track when va arguments begin.
    std::size_t va_args_start_index=0;

    // now assign the argument values to parameters
    for(std::size_t i=0; i<call_arguments.size(); i++)
    {
      if(i<function_parameters.size())
      {
        const code_typet::parametert &function_parameter=function_parameters[i];
        irep_idt identifier=function_parameter.get_identifier();

        if(identifier.empty())
          throw "function_call " + id2string(function_identifier)
              + " no identifier for function parameter";

        symbol_exprt lhs(identifier, function_parameter.type());
        exprt rhs=call_arguments[i];

        // lhs/rhs types might not match
        if(lhs.type()!=rhs.type())
          rhs.make_typecast(lhs.type());

        assign(state, lhs, rhs);
      }
      else if(va_args_start_index==0)
        va_args_start_index=i;
    }

    if(code_type.has_ellipsis())
    {
      std::size_t va_count=0;

      auto call_arguments_it = std::begin(call_arguments);
      std::advance(call_arguments_it, va_args_start_index);
      auto call_arguments_end = std::end(call_arguments);

      for(; call_arguments_it!=call_arguments_end; ++call_arguments_it)
      {
        exprt rhs=*call_arguments_it;

        irep_idt id=id2string(function_identifier)+"::va_arg"
            +std::to_string(va_count);

        // clear the var_state, since the type may have changed
        auto &var_info=state.var_map(id, irep_idt(), rhs.type());
        var_info.type=rhs.type();
        state.get_var_state(var_info).ssa_symbol.set_identifier(irep_idt());

        symbolt symbol;
        symbol.name=id;
        symbol.base_name="va_arg"+std::to_string(va_count);
        symbol.type=rhs.type();

        va_count++;

        symbol_exprt lhs=symbol.symbol_expr();
        assert(lhs.type()==rhs.type());
        assign(state, lhs, rhs);
      }
    }

    // update statistics
    state.recursion_map[function_identifier]++;

    // set the new PC
    thread.pc=function_entry_point;
  }
  else if(function.id()==ID_dereference)
  {
    // should not happen, we read() before
    throw "function_call_rec got dereference";
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
  else
    // NOLINTNEXTLINE(readability/throw)
    throw "TODO: function_call "+function.id_string();
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
    // return function from which we return
    state.history->function_identifier=
      thread.call_stack.back().current_function;

    // update statistics
    state.recursion_map[thread.call_stack.back().current_function]--;

    // set PC to return location
    thread.pc=thread.call_stack.back().return_location;

    // assign the return value
    if(thread.call_stack.back().return_rhs.is_not_nil() &&
       thread.call_stack.back().return_lhs.is_not_nil())
      assign(state, thread.call_stack.back().return_lhs,
                    thread.call_stack.back().return_rhs);

    // restore the local variables
    for(path_symex_statet::var_state_mapt::const_iterator
        it=thread.call_stack.back().saved_local_vars.begin();
        it!=thread.call_stack.back().saved_local_vars.end();
        it++)
      thread.local_vars[it->first]=it->second;

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

  if(instruction.is_backwards_goto())
  {
    // we keep a statistic on how many times we execute backwards gotos
    state.unwinding_map[state.pc()]++;
  }

  const loct &loc=state.locs[state.pc()];
  assert(!loc.branch_target.is_nil());

  exprt ssa_guard=state.read(instruction.guard);

  if(ssa_guard.is_true()) // branch taken always
  {
    state.record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    state.set_pc(loc.branch_target);
    return; // we are done
  }

  if(!ssa_guard.is_false())
  {
    // branch taken case
    // copy the state into 'further_states'
    further_states.push_back(state);
    further_states.back().record_step();
    state.history->branch=stept::BRANCH_TAKEN;
    further_states.back().set_pc(loc.branch_target);
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

  exprt ssa_guard=state.read(instruction.guard);

  if(taken)
  {
    // branch taken case
    const loct &loc=state.locs[state.pc()];
    assert(!loc.branch_target.is_nil());
    state.set_pc(loc.branch_target);
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

    if(instruction.code.operands().size()==1)
      set_return_value(state, instruction.code.op0());

    break;

  case START_THREAD:
    {
      const loct &loc=state.locs[state.pc()];
      assert(!loc.branch_target.is_nil());

      state.record_step();
      state.next_pc();

      // ordering of the following matters due to vector instability
      path_symex_statet::threadt &new_thread=state.add_thread();
      path_symex_statet::threadt &old_thread=
        state.threads[state.get_current_thread()];
      new_thread.pc=loc.branch_target;
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
    throw "THROW not yet implemented"; // NOLINT(readability/throw)

  case ASSUME:
    state.record_step();
    state.next_pc();
    if(instruction.guard.is_false())
      state.make_infeasible();
    else
    {
      exprt ssa_guard=state.read(instruction.guard);
      state.history->ssa_guard=ssa_guard;
    }
    break;

  case ASSERT:
  case SKIP:
  case LOCATION:
  case DEAD:
    state.record_step();
    state.next_pc();
    break;

  case DECL:
    // assigning an RHS of NIL means 'nondet'
    assign(state, to_code_decl(instruction.code).symbol(), nil_exprt());
    state.next_pc();
    break;

  case ATOMIC_BEGIN:
    if(state.inside_atomic_section)
      throw "nested ATOMIC_BEGIN";

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=true;
    break;

  case ATOMIC_END:
    if(!state.inside_atomic_section)
      throw "ATOMIC_END unmatched"; // NOLINT(readability/throw)

    state.record_step();
    state.next_pc();
    state.inside_atomic_section=false;
    break;

  case ASSIGN:
    assign(state, to_code_assign(instruction.code));
    state.next_pc();
    break;

  case FUNCTION_CALL:
    state.record_step();
    function_call(
      state, to_code_function_call(instruction.code), further_states);
    break;

  case OTHER:
    state.record_step();

    {
      const codet &code=instruction.code;
      const irep_idt &statement=code.get_statement();

      if(statement==ID_expression)
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
        // TODO
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
        throw "unexpected OTHER statement: "+id2string(statement);
    }

    state.next_pc();
    break;

  default:
    throw "path_symext: unexpected instruction";
  }
}

void path_symext::operator()(path_symex_statet &state)
{
  std::list<path_symex_statet> further_states;
  operator()(state, further_states);
  if(!further_states.empty())
    throw "path_symext got unexpected further states";
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
