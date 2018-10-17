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
    if(step_ref->ssa_guard.is_not_nil() &&
       !step_ref->ssa_guard.is_true())
    {
      out << faint << "{-" << count << "} " << reset
          << format(step_ref->ssa_guard) << '\n';
      count++;
    }

    if(step_ref->ssa_rhs.is_not_nil())
    {
      equal_exprt equality(step_ref->ssa_lhs, step_ref->ssa_rhs);
      out << faint << "{-" << count << "} " << reset
          << format(equality) << '\n';
      count++;
    }
  }

  // Unicode equivalent of "|--------------------------"
  out << faint << u8"\u251c";
  for(unsigned i = 0; i < 26; i++)
    out << u8"\u2500";
  out << reset << '\n';

  exprt assertion=state.read(instruction.guard);

  out << faint << "{" << 1 << "} " << reset
      << format(assertion) << '\n';

  if(!assertion.is_true())
    number_of_VCCs_after_simplification++;

  out << eom;
}
