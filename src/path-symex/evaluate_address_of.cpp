/*******************************************************************\

Module: Address Canonicalization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "evaluate_address_of.h"

#include <util/pointer_offset_size.h>
#include <util/c_types.h>

exprt add_offset(const exprt &base, const exprt &offset)
{
  pointer_typet char_pointer=pointer_type(char_type());
  const exprt base_casted=
    typecast_exprt::conditional_cast(base, char_pointer);
  return plus_exprt();
}

exprt index_offset_expr(const index_exprt &src, const namespacet &ns)
{
  const exprt element_size=size_of_expr(src.type(), ns);
  return mult_exprt(src.index(), element_size);
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
    const exprt offset=index_offset_expr(index_expr, ns);
    const exprt base=evaluate_address_of_rec(index_expr.array(), ns);
    return plus_exprt(base, offset);
  }
  else if(src.id()==ID_dereference)
  {
    return to_dereference_expr(src).pointer();
  }
  else
    return address_of_exprt(src);
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
