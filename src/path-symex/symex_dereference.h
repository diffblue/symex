/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_SYMEX_DEREFERENCE_H
#define CPROVER_SYMEX_DEREFERENCE_H

#include <util/namespace.h>
#include <util/expr.h>

class if_exprt;
class typecast_exprt;

/*! \brief TO_BE_DOCUMENTED
*/
class symex_dereferencet
{
public:
  /*! \brief Constructor
   * \param _ns Namespace
   * \param _new_symbol_table A symbol_table to store new symbols in
   * \param _options Options, in particular whether pointer checks are
            to be performed
   * \param _dereference_callback Callback object for error reporting
  */
  explicit symex_dereferencet(
    const namespacet &_ns):
    ns(_ns)
  {
  }

  ~symex_dereferencet() { }

  /*!
   * The operator '()' dereferences the
   * given pointer-expression.
   *
   * \param pointer A pointer-typed expression, to
            be dereferenced.
  */

  exprt operator()(const exprt &pointer);

private:
  const namespacet &ns;

  exprt dereference_rec(
    const exprt &address,
    const exprt &offset,
    const typet &type);

  exprt dereference_if(
    const if_exprt &expr,
    const exprt &offset,
    const typet &type);

  exprt dereference_plus(
    const exprt &expr,
    const exprt &offset,
    const typet &type);

  exprt dereference_typecast(
    const typecast_exprt &expr,
    const exprt &offset,
    const typet &type);

  bool type_compatible(
    const typet &object_type,
    const typet &dereference_type) const;

  void offset_sum(
    exprt &dest,
    const exprt &offset) const;

  exprt read_object(
    const exprt &object,
    const exprt &offset,
    const typet &type);
};

inline exprt symex_dereference(const exprt &pointer, const namespacet &ns)
{
  symex_dereferencet dereference_object(ns);
  return dereference_object(pointer);
}

#endif // CPROVER_SYMEX_DEREFERENCE_H
