/*******************************************************************\

Module: Build Goto Trace from State History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Build Goto Trace from State History

#include <util/simplify_expr.h>

#include "build_goto_trace.h"

/// follow state history to build a goto trace
goto_tracet build_goto_trace(
  const path_symex_statet &state,
  const decision_proceduret &decision_procedure)
{
  // follow the history in the state,
  // but in a forwards-fashion

  std::vector<path_symex_step_reft> steps;
  state.history.build_history(steps);

  goto_tracet goto_trace;

  for(std::size_t step_nr=0; step_nr<steps.size(); step_nr++)
  {
    const path_symex_stept &step=*steps[step_nr];

    goto_trace_stept trace_step;

    assert(!step.pc.is_nil());
    trace_step.pc=state.config.locs[step.pc].target;
    trace_step.function=step.f_identifier;
    trace_step.thread_nr=step.thread_nr;
    trace_step.step_nr=step_nr;
    trace_step.hidden=step.hidden;

    const goto_programt::instructiont &instruction=*trace_step.pc;

    switch(instruction.type)
    {
    case ASSIGN:
      if(step.lhs.type().id()==ID_array &&
         step.ssa_rhs.id()==ID_with)
      {
        // this is an unbounded array, assigned as
        //  new_array = old_array WITH [index:=value]
        //
        // instead process as
        //  new_array[index] = value
        const exprt index_ssa=to_with_expr(step.ssa_rhs).where();
        const exprt index_value=decision_procedure.get(index_ssa);
        trace_step.full_lhs=index_exprt(step.lhs, index_value);
        trace_step.full_lhs_value=
          simplify_expr(decision_procedure.get(index_exprt(step.ssa_lhs, index_ssa)),
                        state.config.ns);
      }
      else
      {
        trace_step.full_lhs=step.lhs;
        trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
      }

      trace_step.type=goto_trace_stept::typet::ASSIGNMENT;
      trace_step.assignment_type=goto_trace_stept::assignment_typet::STATE;
      break;

    case DECL:
      trace_step.type=goto_trace_stept::typet::DECL;
      trace_step.full_lhs=step.lhs;
      trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
      trace_step.assignment_type=goto_trace_stept::assignment_typet::STATE;
      break;

    case DEAD:
      trace_step.type=goto_trace_stept::typet::DEAD;
      break;

    case ASSUME:
      trace_step.type=goto_trace_stept::typet::ASSUME;
      trace_step.cond_value = true;
      break;

    case FUNCTION_CALL:
      // these have parameter assignments!
      if(step.lhs.is_not_nil())
      {
        trace_step.type=goto_trace_stept::typet::ASSIGNMENT;
        trace_step.full_lhs=step.lhs;
        trace_step.full_lhs_value=decision_procedure.get(step.ssa_lhs);
        trace_step.assignment_type=
          goto_trace_stept::assignment_typet::ACTUAL_PARAMETER;
        // trace_step.lhs_object and trace_step.lhs_object_value
        // are not filled
      }
      else
      {
        trace_step.type=goto_trace_stept::typet::FUNCTION_CALL;
        trace_step.called_function=step.called_function;
        trace_step.function_arguments.resize(step.function_arguments.size());
        for(std::size_t i=0; i<trace_step.function_arguments.size(); i++)
          trace_step.function_arguments[i]=decision_procedure.get(step.function_arguments[i].ssa_lhs);
      }
      break;

    case END_FUNCTION:
      trace_step.type=goto_trace_stept::typet::FUNCTION_RETURN;
      break;

    case START_THREAD:
      trace_step.type=goto_trace_stept::typet::SPAWN;
      break;

    case ATOMIC_BEGIN:
      trace_step.type=goto_trace_stept::typet::ATOMIC_BEGIN;
      break;

    case ATOMIC_END:
      trace_step.type=goto_trace_stept::typet::ATOMIC_END;
      break;

    default:
      trace_step.type=goto_trace_stept::typet::LOCATION;
    }

    goto_trace.add_step(trace_step);
  }

  return goto_trace;
}
