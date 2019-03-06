/*******************************************************************\

Module: State of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// State of path-based symbolic simulator

#include "path_symex_state.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/decision_procedure.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

#ifdef DEBUG
#include <iostream>
#endif

void path_symex_statet::output(const threadt &thread, std::ostream &out) const
{
  out << "  PC: " << thread.pc << '\n';
  out << "  Call stack:";

  for(const auto &frame : thread.call_stack)
    out << " " << frame.return_location;

  out << '\n';
}

void path_symex_statet::output(std::ostream &out) const
{
  for(const auto &v : shared_vars)
    if(!v.ssa_symbol.get_identifier().empty())
    {
      out << from_expr(v.ssa_symbol);
      if(v.value.is_not_nil())
        out << " = " << from_expr(v.value);
      out << '\n';
    }

  for(unsigned t=0; t<threads.size(); t++)
  {
    out << "*** Thread " << t << '\n';
    output(threads[t], out);
    out << '\n';
  }
}

path_symex_statet::var_statet &path_symex_statet::get_var_state(
  const var_mapt::var_infot &var_info)
{
  assert(current_thread<threads.size());

  var_valt &var_val=
    var_info.is_shared()?shared_vars:threads[current_thread].local_vars;
  if(var_val.size()<=var_info.number)
    var_val.resize(var_info.number+1);
  return var_val[var_info.number];
}

template<typename T>
void path_symex_statet::record_step(T variant)
{
  // is there a context switch happening?
  if(!history.is_nil() &&
     history->thread_nr!=current_thread)
    no_thread_interleavings++;

  // add the step
  history.generate_successor(std::move(variant));
  stept &step=*history;

  // copy PC
  assert(current_thread<threads.size());
  const auto &thread=threads[current_thread];
  step.pc=thread.pc;
  step.f_identifier=thread.function_id;
  step.thread_nr=current_thread;

  // set hide flag
  step.hidden=get_hide();
}

bool path_symex_statet::is_feasible(
  decision_proceduret &decision_procedure) const
{
  // feed path constraint to decision procedure
  decision_procedure << history;

  // check whether SAT
  switch(decision_procedure())
  {
  case decision_proceduret::resultt::D_SATISFIABLE: return true;

  case decision_proceduret::resultt::D_UNSATISFIABLE: return false;

  case decision_proceduret::resultt::D_ERROR:
    throw "error from decision procedure";
  }

  return true; // not really reachable
}

bool path_symex_statet::check_assertion(
  decision_proceduret &decision_procedure)
{
  const goto_programt::instructiont &instruction=*get_instruction();

  // assert that this is an assertion
  assert(instruction.is_assert());

  // the assertion in SSA
  exprt assertion=read(instruction.get_condition());

  // trivial?
  if(assertion.is_true())
    return true; // no error

  // the path constraint
  decision_procedure << history;

  // negate the assertion
  decision_procedure.set_to(assertion, false);

  // check whether SAT
  switch(decision_procedure.dec_solve())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    return false; // error

  case decision_proceduret::resultt::D_UNSATISFIABLE:
    return true; // no error

  default:
    throw "error from decision procedure";
  }

  return true; // not really reachable
}
