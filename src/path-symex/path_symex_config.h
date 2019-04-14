/*******************************************************************\

Module: Configuration of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// State of path-based symbolic simulator

#ifndef CPROVER_PATH_SYMEX_PATH_SYMEX_CONFIG_H
#define CPROVER_PATH_SYMEX_PATH_SYMEX_CONFIG_H

#include "var_map.h"
#include "path_symex_history.h"

#include <util/message.h>

#include <goto-programs/goto_functions.h>

#include <set>

struct path_symex_statet;

struct path_symex_configt:public messaget
{
public:
  explicit path_symex_configt(
    const namespacet &_ns,
    const goto_functionst &_goto_functions):
    ns(_ns),
    goto_functions(_goto_functions),
    var_map(_ns)
  {
  }

  const namespacet &ns;
  const goto_functionst &goto_functions;
  var_mapt var_map;
  path_symex_historyt path_symex_history;

  path_symex_statet initial_state();

protected:
  std::set<irep_idt> body_warnings;
  void no_body(const irep_idt &);
  
  friend class path_symext;
};

#endif // CPROVER_PATH_SYMEX_PATH_SYMEX_CONFIG_H
