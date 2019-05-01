/*******************************************************************\

Module: Configuration of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Configuration of path-based symbolic simulator

#include "path_symex_config.h"
#include "path_symex_state.h"

goto_functionst::function_mapt::const_iterator
path_symex_configt::get_function(const irep_idt &identifier)
{
  // trigger the hook
  if(load_function != nullptr)
    load_function(identifier);

  // find the function
  auto f_it = goto_functions.function_map.find(identifier);

  if(f_it==goto_functions.function_map.end())
    throw
      "failed to find `"+id2string(identifier)+"' in function_map";

  return f_it;
}

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

  // look that up
  auto f_it = goto_functions.function_map.find(entry_function);
  if(f_it == goto_functions.function_map.end())
    throw "no entry point";

  if(!f_it->second.body_available())
    throw "no entry point";

  if(f_it->second.body.instructions.empty())
    throw "no entry point";

  path_symex_statet s(*this);

  // create one new thread
  path_symex_statet::threadt &thread=s.add_thread();
  thread.pc=loc_reft(entry_function, f_it->second.body.instructions.begin()); // set its PC

  if(thread.pc.is_nil())
    throw "no entry point";

  s.set_current_thread(0);
  s.history=path_symex_step_reft(path_symex_history);

  return s;
}
