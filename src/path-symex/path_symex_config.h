/*******************************************************************\

Module: Configuration of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// State of path-based symbolic simulator

#ifndef CPROVER_PATH_SYMEX_PATH_SYMEX_CONFIG_H
#define CPROVER_PATH_SYMEX_PATH_SYMEX_CONFIG_H

#include <util/message.h>

#include <set>

struct path_symex_configt:public messaget
{
public:

protected:
  std::set<irep_idt> body_warnings;
  void no_body(const irep_idt &);
  
  friend class path_symext;
};

#endif // CPROVER_PATH_SYMEX_PATH_SYMEX_STATE_H
