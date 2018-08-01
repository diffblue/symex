/*******************************************************************\

Module: Configuration of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Configuration of path-based symbolic simulator

#include "path_symex_config.h"

void path_symex_configt::no_body(const irep_idt &identifier)
{
  if(body_warnings.insert(identifier).second)
  {
    warning() << "**** WARNING: no body for function "
              << identifier << eom;
  }
}
