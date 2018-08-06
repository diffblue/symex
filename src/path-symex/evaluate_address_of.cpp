/*******************************************************************\

Module: Address Canonicalization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "evaluate_address_of.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_offset_size.h>

static exprt add_offset(const exprt &base, const exprt &offset)
{
  pointer_typet char_pointer=pointer_type(char_type());
  const exprt base_casted=
    typecast_exprt::conditional_cast(base, char_pointer);
  return plus_exprt();
}

exprt evaluate_address_of_rec(
  const exprt &src,
  const namespacet &ns)
{
  if(src.id()==ID_member)
  {
    const auto &member_expr=to_member_expr(src);
    const exprt offset=member_offset_expr(member_expr, ns);
    const exprt base=evaluate_address_of_rec(member_expr.compound(), ns);
    return add_offset(base, offset);
  }
  else if(src.id()==ID_index)
  {
    const auto &index_expr=to_index_expr(src);
    const exprt base=
      typecast_exprt::conditional_cast(
        evaluate_address_of_rec(index_expr.array(), ns),
        pointer_type(index_expr.type()));
    return plus_exprt(base, index_expr.index());
  }
  else if(src.id()==ID_dereference)
  {
    return to_dereference_expr(src).pointer();
  }
  else if(src.id()==ID_if)
  {
    if_exprt new_if_expr=to_if_expr(src);
    new_if_expr.true_case()=
      evaluate_address_of_rec(new_if_expr.true_case(), ns);
    new_if_expr.false_case()=
      evaluate_address_of_rec(new_if_expr.false_case(), ns);
    new_if_expr.type()=pointer_type(src.type());
    return new_if_expr;
  }
  else
  {
    if(src.type().id()==ID_array)
      return typecast_exprt(address_of_exprt(src), pointer_type(src.type().subtype()));
    else
      return address_of_exprt(src);
  }
}

exprt evaluate_address_of(
  const address_of_exprt &src,
  const namespacet &ns)
{
  if(src.object().id()==ID_symbol)
    return src;
  else
    return typecast_exprt::conditional_cast(
      evaluate_address_of_rec(src.object(), ns),
      src.type());
}
