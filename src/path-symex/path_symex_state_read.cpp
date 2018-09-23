/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// State of path-based symbolic simulator

#include "path_symex_state.h"

#include <util/simplify_expr.h>
#include <util/arith_tools.h>

#include <pointer-analysis/dereference.h>

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include "evaluate_address_of.h"

exprt path_symex_statet::read(const exprt &src, bool propagate)
{
  #ifdef DEBUG
  std::cout << "path_symex_statet::read " << from_expr(src) << '\n';
  #endif

  // This has three phases!
  // 1. Dereferencing, including propagation of pointers.
  // 2. Rewriting to SSA symbols
  // 3. Simplifier

  // we force propagation for dereferencing
  exprt tmp3=dereference_rec(src, true);

  exprt tmp4=instantiate_rec(tmp3, propagate);

  exprt tmp5=simplify_expr(tmp4, config.ns);

  #ifdef DEBUG
  std::cout << " ==> " << from_expr(tmp5) << '\n';
  #endif

  return tmp5;
}

exprt path_symex_statet::expand_structs_and_arrays(const exprt &src)
{
  #ifdef DEBUG
  std::cout << "expand_structs_and_arrays: "
            << from_expr(config.ns, "", src) << '\n';
  #endif

  const typet &src_type=config.ns.follow(src.type());

  if(src_type.id()==ID_struct) // src is a struct
  {
    const struct_typet &struct_type=to_struct_type(src_type);
    const struct_typet::componentst &components=struct_type.components();

    struct_exprt result(src.type());
    result.operands().resize(components.size());

    // split it up into components
    for(unsigned i=0; i<components.size(); i++)
    {
      const typet &subtype=components[i].type();
      const irep_idt &component_name=components[i].get_name();

      exprt new_src;
      if(src.id()==ID_struct) // struct constructor?
      {
        assert(src.operands().size()==components.size());
        new_src=src.operands()[i];
      }
      else
        new_src=member_exprt(src, component_name, subtype);

      // recursive call
      result.operands()[i]=expand_structs_and_arrays(new_src);
    }

    return result; // done
  }
  else if(src_type.id()==ID_array) // src is an array
  {
    const array_typet &array_type=to_array_type(src_type);
    const typet &subtype=array_type.subtype();

    if(array_type.size().is_constant())
    {
      mp_integer size;
      if(to_integer(array_type.size(), size))
        throw "failed to convert array size";

      std::size_t size_int=integer2size_t(size);

      array_exprt result(array_type);
      result.operands().resize(size_int);

      // split it up into elements
      for(std::size_t i=0; i<size_int; ++i)
      {
        exprt index=from_integer(i, array_type.size().type());
        exprt new_src=index_exprt(src, index, subtype);

        // array constructor?
        if(src.id()==ID_array)
          new_src=simplify_expr(new_src, config.ns);

        // recursive call
        result.operands()[i]=expand_structs_and_arrays(new_src);
      }

      return result; // done
    }
    else
    {
      // TODO: variable-sized array
    }
  }
  else if(src_type.id()==ID_vector) // src is a vector
  {
    const vector_typet &vector_type=to_vector_type(src_type);
    const typet &subtype=vector_type.subtype();

    if(!vector_type.size().is_constant())
      throw "vector with non-constant size";

    mp_integer size;
    if(to_integer(vector_type.size(), size))
      throw "failed to convert vector size";

    std::size_t size_int=integer2size_t(size);

    vector_exprt result(vector_type);
    exprt::operandst &operands=result.operands();
    operands.resize(size_int);

    // split it up into elements
    for(std::size_t i=0; i<size_int; ++i)
    {
      exprt index=from_integer(i, vector_type.size().type());
      exprt new_src=index_exprt(src, index, subtype);

      // vector constructor?
      if(src.id()==ID_vector)
        new_src=simplify_expr(new_src, config.ns);

      // recursive call
      operands[i]=expand_structs_and_arrays(new_src);
    }

    return result; // done
  }

  return src;
}

exprt path_symex_statet::array_theory(const exprt &src, bool propagate)
{
  if(src.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(src);
    const array_typet &array_type=to_array_type(index_expr.array().type());

    if(var_mapt::is_unbounded_array(array_type))
    {
    }
    else
    {
      exprt index_tmp1=read(index_expr.index(), propagate);
      exprt index_tmp2=simplify_expr(index_tmp1, config.ns);

      if(!index_tmp2.is_constant())
      {
        const typet &subtype=array_type.subtype();

        mp_integer size;
        if(to_integer(array_type.size(), size))
          throw "failed to convert array size";

        std::size_t size_int=integer2size_t(size);

        exprt result=nil_exprt();

        // split it up
        for(std::size_t i=0; i<size_int; ++i)
        {
          exprt index=from_integer(i, index_expr.index().type());
          exprt new_src=index_exprt(index_expr.array(), index, subtype);

          if(result.is_nil())
            result=new_src;
          else
          {
            equal_exprt index_equal(index_expr.index(), index);
            result=if_exprt(index_equal, new_src, result);
          }
        }

        return result; // done
      }
    }
  }

  return src;
}

exprt path_symex_statet::instantiate_rec(
  const exprt &src,
  bool propagate)
{
  #ifdef DEBUG
  std::cout << "instantiate_rec: "
            << from_expr(config.ns, "", src) << '\n';
  #endif

  // check whether this is a symbol(.member|[index])*

  if(is_symbol_member_index(src))
  {
    exprt tmp_symbol_member_index=
      read_symbol_member_index(src, propagate);

    assert(tmp_symbol_member_index.is_not_nil());
    return tmp_symbol_member_index; // yes!
  }

  if(src.id()==ID_address_of)
  {
    // these have already been flattened out by dereference_rec
    return src;
  }
  else if(src.id()==ID_side_effect)
  {
    // could be done separately
    const irep_idt &statement=to_side_effect_expr(src).get_statement();

    if(statement==ID_nondet)
    {
      irep_idt id="symex::nondet"+std::to_string(config.var_map.nondet_count);
      config.var_map.nondet_count++;

      auxiliary_symbolt nondet_symbol;
      nondet_symbol.name=id;
      nondet_symbol.base_name=id;
      nondet_symbol.type=src.type();
      config.var_map.new_symbols.add(nondet_symbol);

      return nondet_symbol.symbol_expr();
    }
    else
      throw "instantiate_rec: unexpected side effect "+id2string(statement);
  }
  else if(src.id()==ID_dereference)
  {
    // dereferencet has run already, so we should only be left with
    // integer addresses. Will transform into __CPROVER_memory[]
    // eventually.
  }
  else if(src.id()==ID_integer_dereference)
  {
    // dereferencet produces these for stuff like *(T *)123.
    // Will transform into __CPROVER_memory[] eventually.
    irep_idt id="symex::deref"+std::to_string(config.var_map.nondet_count);
    config.var_map.nondet_count++;

    auxiliary_symbolt nondet_symbol;
    nondet_symbol.name=id;
    nondet_symbol.base_name=id;
    nondet_symbol.type=src.type();
    config.var_map.new_symbols.add(nondet_symbol);

    return nondet_symbol.symbol_expr();
  }
  else if(src.id()==ID_member)
  {
    const typet &compound_type=
      config.ns.follow(to_member_expr(src).struct_op().type());

    if(compound_type.id()==ID_struct)
    {
      // do nothing
    }
    else if(compound_type.id()==ID_union)
    {
      // should already have been rewritten to byte_extract
      throw "unexpected union member";
    }
    else
    {
      throw "member expects struct or union type"+src.pretty();
    }
  }
  else if(src.id()==ID_byte_extract_little_endian ||
          src.id()==ID_byte_extract_big_endian)
  {
  }
  else if(src.id()==ID_symbol)
  {
    // must be SSA already, or code
    assert(src.type().id()==ID_code ||
           src.get_bool(ID_C_SSA_symbol));
  }
  else if(src.id()=="dereference_error")
  {
    irep_idt id="symex::deref"+std::to_string(config.var_map.nondet_count);
    config.var_map.nondet_count++;

    auxiliary_symbolt nondet_symbol;
    nondet_symbol.name=id;
    nondet_symbol.base_name=id;
    nondet_symbol.type=src.type();
    config.var_map.new_symbols.add(nondet_symbol);

    return nondet_symbol.symbol_expr();
  }

  if(!src.has_operands())
    return src;

  exprt src2=src;

  // recursive calls on structure of 'src'
  Forall_operands(it, src2)
  {
    exprt tmp_op=instantiate_rec(*it, propagate);
    *it=tmp_op;
  }

  return src2;
}

exprt path_symex_statet::read_symbol_member_index(
  const exprt &src,
  bool propagate)
{
  const typet &src_type=config.ns.follow(src.type());

  // don't touch function symbols
  if(src_type.id()==ID_code)
    return nil_exprt();

  // unbounded array?
  if(src.id()==ID_index &&
     var_mapt::is_unbounded_array(to_index_expr(src).array().type()))
  {
    index_exprt new_src=to_index_expr(src);
    new_src.array()=read_symbol_member_index(new_src.array(), propagate); // rec. call
    new_src.index()=instantiate_rec(new_src.index(), propagate); // rec. call
    return new_src;
  }

  // is this a struct/array/vector that needs to be expanded?
  exprt final=expand_structs_and_arrays(src);

  if(final.id()==ID_struct ||
     final.id()==ID_array ||
     final.id()==ID_vector)
  {
    Forall_operands(it, final)
      *it=read_symbol_member_index(*it, propagate); // rec. call

    return final;
  }

  // now do array theory
  final=array_theory(final, propagate);

  if(final.id()==ID_if)
  {
    assert(final.operands().size()==3);
    final.op0()=instantiate_rec(final.op0(), propagate); // rec. call
    final.op1()=read_symbol_member_index(final.op1(), propagate); // rec. call
    final.op2()=read_symbol_member_index(final.op2(), propagate); // rec. call
    return final;
  }

  std::string suffix="";
  exprt current=src;

  // the loop avoids recursion
  while(current.id()!=ID_symbol)
  {
    exprt next=nil_exprt();

    if(current.id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(current);

      const typet &compound_type=
        config.ns.follow(member_expr.struct_op().type());

      if(compound_type.id()==ID_struct)
      {
        // go into next iteration
        next=member_expr.struct_op();
        suffix="."+id2string(member_expr.get_component_name())+suffix;
      }
      else
        return nil_exprt(); // includes unions, deliberately
    }
    else if(current.id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(current);

      exprt index_tmp=read(index_expr.index(), propagate);

      std::string index_string=array_index_as_string(index_tmp);

      // go into next iteration
      next=index_expr.array();
      suffix=index_string+suffix;
    }
    else
      return nil_exprt();

    // next round
    assert(next.is_not_nil());
    current=next;
  }

  assert(current.id()==ID_symbol);

  if(current.get_bool(ID_C_SSA_symbol))
    return nil_exprt(); // SSA already

  irep_idt identifier=
    to_symbol_expr(current).get_identifier();

  var_mapt::var_infot &var_info=
    config.var_map(identifier, suffix, src);

  #ifdef DEBUG
  std::cout << "read_symbol_member_index_rec " << identifier
            << " var_info " << var_info.full_identifier << '\n';
  #endif

  // warning: reference is not stable
  var_statet &var_state=get_var_state(var_info);

  if(propagate && var_state.value.is_not_nil())
  {
    return var_state.value; // propagate a value
  }
  else
  {
    // we do some SSA symbol
    if(var_state.ssa_symbol.get_identifier().empty())
    {
      // produce one
      var_state.ssa_symbol=var_info.ssa_symbol();

      // ssa-ify the size
      if(var_mapt::is_unbounded_array(var_state.ssa_symbol.type()))
      {
        exprt &size=to_array_type(var_state.ssa_symbol.type()).size();
        size=read(size);
      }
    }

    return var_state.ssa_symbol;
  }
}

bool path_symex_statet::is_symbol_member_index(const exprt &src) const
{
  const typet final_type=src.type();

  // don't touch function symbols
  if(config.ns.follow(final_type).id()==ID_code)
    return false;

  const exprt *current=&src;

  // the loop avoids recursion
  while(true)
  {
    const exprt *next=nullptr;

    if(current->id()==ID_symbol)
    {
      if(current->get_bool(ID_C_SSA_symbol))
        return false; // SSA already

      return true;
    }
    else if(current->id()==ID_member)
    {
      const member_exprt &member_expr=to_member_expr(*current);

      const typet &compound_type=
        config.ns.follow(member_expr.struct_op().type());

      if(compound_type.id()==ID_struct)
      {
        // go into next iteration
        next=&(member_expr.struct_op());
      }
      else
        return false; // includes unions, deliberately
    }
    else if(current->id()==ID_index)
    {
      const index_exprt &index_expr=to_index_expr(*current);

      // go into next iteration
      next=&(index_expr.array());
    }
    else
      return false;

    // next round
    INVARIANT_STRUCTURED(next!=nullptr, nullptr_exceptiont, "next is null");
    current=next;
  }
}

std::string path_symex_statet::array_index_as_string(const exprt &src) const
{
  exprt tmp=simplify_expr(src, config.ns);
  mp_integer i;

  if(src.id()==ID_constant && !to_integer(tmp, i))
    return "["+integer2string(i)+"]";
  else
    return "[*]";
}

exprt path_symex_statet::dereference_rec(
  const exprt &src,
  bool propagate)
{
  if(src.id()==ID_dereference)
  {
    const dereference_exprt &dereference_expr=to_dereference_expr(src);

    // read the address to propagate the pointers
    exprt address=read(dereference_expr.pointer(), propagate);

    // now hand over to dereference
    exprt address_dereferenced=::dereference(address, config.ns);

    // the dereferenced address is a mixture of non-SSA and SSA symbols
    // (e.g., if-guards and array indices)
    return address_dereferenced;
  }
  else if(src.id()==ID_address_of)
  {
    const auto &address_of_expr=to_address_of_expr(src);
    const exprt tmp=evaluate_address_of(address_of_expr, config.ns);

    if(tmp.id()==ID_address_of)
      return src; // no change
    else
      return dereference_rec(tmp, propagate);
  }

  if(!src.has_operands())
    return src;

  exprt src2=src;

  {
    // recursive calls on structure of 'src'
    Forall_operands(it, src2)
    {
      exprt tmp_op=dereference_rec(*it, propagate);
      *it=tmp_op;
    }
  }

  return src2;
}

