/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Path-based Symbolic Execution

#include "path_search.h"

#include <util/format_expr.h>

void path_searcht::do_show_vcc(statet &state)
{
  // keep statistics
  number_of_VCCs++;

  const goto_programt::instructiont &instruction=
    *state.get_instruction();

  mstreamt &out=result();

  if(instruction.source_location.is_not_nil())
    out << instruction.source_location << '\n';

  if(instruction.source_location.get_comment()!="")
    out << instruction.source_location.get_comment() << '\n';

  std::size_t count=1;

  std::vector<path_symex_step_reft> steps;
  state.history.build_history(steps);

  for(const auto &step_ref : steps)
  {
    if(step_ref->is_branch() || step_ref->is_assume())
    {
      const exprt c =
        step_ref->is_branch() ? step_ref->branch().ssa_cond : step_ref->assume().ssa_cond;

      if(!c.is_true())
      {
        out << faint << "{-" << count << "} " << reset
            << format(c) << '\n';
        count++;
      }
    }

    if(step_ref->is_assign())
    {
      const auto &a = step_ref->assign();
      out << faint << "{-" << count << "} " << reset
          << format(equal_exprt(a.ssa_lhs, a.ssa_rhs)) << '\n';
      count++;
    }
  }

  // Unicode equivalent of "|--------------------------"
  out << faint << u8"\u251c";
  for(unsigned i = 0; i < 26; i++)
    out << u8"\u2500";
  out << reset << '\n';

  const exprt assertion=state.read(instruction.get_condition());

  const exprt::operandst disjuncts =
    assertion.id() == ID_or ? assertion.operands() :
    exprt::operandst({ assertion });

  count = 1;
  for(const auto &d : disjuncts)
  {
    out << faint << "{" << count << "} " << reset
        << format(d) << '\n';
    count++;
  }

  if(!assertion.is_true())
    number_of_VCCs_after_simplification++;

  out << eom;
}
