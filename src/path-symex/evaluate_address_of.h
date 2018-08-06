/*******************************************************************\

Module: Address Canonicalization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EVALUATE_ADDRESS_OF_H
#define CPROVER_EVALUATE_ADDRESS_OF_H

#include <util/std_expr.h>

class namespacet;

exprt evaludate_address_of(const address_of_exprt &, const namespacet &);

#endif // CPROVER_EVALUATE_ADDRESS_OF_H

