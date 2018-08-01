/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Concrete Symbolic Transformer

#include "path_symex_class.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/pointer_offset_size.h>

inline static typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil())
        return t;
    }
  }

  return nil_typet();
}

void path_symext::symex_allocate(
  path_symex_statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=2)
    throw "allocate expected to have two operands";

  if(code.type().id()!=ID_pointer)
    throw "allocate expected to return a pointer";

  // get a mode, from the call site
  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  const symbolt &calling_function=
    state.config.ns.lookup(instruction.function);

  const irep_idt &mode=calling_function.mode;

  // increment dynamic object counter
  unsigned dynamic_count=++state.config.var_map.dynamic_count;

  exprt size=code.op0();
  typet object_type=nil_typet();

  // is the object type given as return type?
  if(code.type().id()==ID_pointer &&
     code.type().subtype().id()!=ID_empty)
  {
    object_type=code.type().subtype();
  }
  else
  {
    exprt tmp_size=state.read(size); // to allow constant propagation

    // special treatment for sizeof(T)*x
    if(tmp_size.id()==ID_mult &&
       tmp_size.operands().size()==2 &&
       tmp_size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(tmp_size.op0()),
        tmp_size.op1());
    }
    else
    {
      typet tmp_type=c_sizeof_type_rec(tmp_size);

      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(tmp_type, state.config.ns);
        mp_integer alloc_size;
        if(elem_size<0 || to_integer(tmp_size, alloc_size))
        {
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;

            if(elements*elem_size==alloc_size)
              object_type=
                array_typet(tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }

    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), tmp_size);

    // we introduce a fresh symbol for the size
    // to prevent any issues of the size getting ever changed

    if(object_type.id()==ID_array &&
       !to_array_type(object_type).size().is_constant())
    {
      exprt &size=to_array_type(object_type).size();

      symbolt size_symbol;

      size_symbol.base_name="dynamic_object_size"+std::to_string(dynamic_count);
      size_symbol.name="symex::"+id2string(size_symbol.base_name);
      size_symbol.is_lvalue=true;
      size_symbol.type=tmp_size.type();
      size_symbol.mode=mode;

      assign(state,
             size_symbol.symbol_expr(),
             size);

      size=size_symbol.symbol_expr();
    }
  }

  // value
  symbolt value_symbol;

  value_symbol.base_name=
    "dynamic_object"+std::to_string(state.config.var_map.dynamic_count);
  value_symbol.name="symex_dynamic::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=object_type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=mode;

  exprt rhs;

  if(object_type.id()==ID_array)
  {
    index_exprt index_expr(value_symbol.type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=from_integer(0, index_type());
    rhs=address_of_exprt(
      index_expr, pointer_type(value_symbol.type.subtype()));
  }
  else
  {
    rhs=address_of_exprt(
      value_symbol.symbol_expr(), pointer_type(value_symbol.type));
  }

  // zero initialized?
  exprt initialize=state.read(code.op1());
  mp_integer initialize_i;
  if(!to_integer(initialize, initialize_i) &&
     initialize_i==1)
  {
    exprt zero=zero_initializer(
      value_symbol.type,
      code.source_location(),
      state.config.ns);

    if(zero.is_not_nil())
    {
      assign(state, value_symbol.symbol_expr(), zero);
    }
  }

  if(rhs.type()!=lhs.type())
    rhs.make_typecast(lhs.type());

  assign(state, lhs, rhs);
}

void path_symext::symex_new(
  path_symex_statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=0)
    throw "new expected to have no operands";

  if(code.type().id()!=ID_pointer)
    throw "new expected to return a pointer";

  const auto &pointer_type = to_pointer_type(code.type());

  const irep_idt &statement=code.get_statement();

  const irep_idt mode=
    statement==ID_java_new_array_data?ID_java:ID_C;

  const bool do_array =
    (code.get(ID_statement) == ID_cpp_new_array ||
     code.get(ID_statement) == ID_java_new_array_data);

  typet type;

  if(do_array)
  {
    exprt size_arg = static_cast<const exprt &>(code.find(ID_size));
    type = array_typet(pointer_type.subtype(), size_arg);
  }
  else
    type = pointer_type.subtype();

  // increment dynamic object counter
  const unsigned dynamic_count=++state.config.var_map.dynamic_count;

  // value
  symbolt value_symbol;

  value_symbol.base_name="dynamic_object"+std::to_string(dynamic_count);
  value_symbol.name="symex_dynamic::"+id2string(value_symbol.base_name);
  value_symbol.is_lvalue=true;
  value_symbol.type=type;
  value_symbol.type.set("#dynamic", true);
  value_symbol.mode=mode;

  exprt rhs;

  if(do_array)
  {
    index_exprt index_expr(pointer_type.subtype());
    index_expr.array()=value_symbol.symbol_expr();
    index_expr.index()=from_integer(0, index_type());
    rhs=address_of_exprt(index_expr, pointer_type);
  }
  else
  {
    rhs=address_of_exprt(value_symbol.symbol_expr(), pointer_type);
  }

  assign(state, lhs, rhs);
}
