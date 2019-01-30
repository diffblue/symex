/*******************************************************************\

Module: Configuration of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Configuration of path-based symbolic simulator

#include "path_symex_config.h"
#include "path_symex_state.h"

void path_symex_configt::no_body(const irep_idt &identifier)
{
  if(body_warnings.insert(identifier).second)
  {
    warning() << "**** WARNING: no body for function "
              << identifier << eom;
  }
}

path_symex_statet path_symex_configt::initial_state()
{
  const irep_idt entry_function = goto_functionst::entry_point();

  path_symex_statet s(*this);

  // create one new thread
  path_symex_statet::threadt &thread=s.add_thread();
  thread.pc=locs.first_loc(entry_function); // set its PC
  thread.function_id=entry_function;

  if(thread.pc.is_nil())
    throw "no entry point";

  s.set_current_thread(0);
  s.history=path_symex_step_reft(path_symex_history);

  return s;
}
