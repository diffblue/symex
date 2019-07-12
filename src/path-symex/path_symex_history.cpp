/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// History of path-based symbolic simulator

#include "path_symex_history.h"

#include <algorithm>

#include <solvers/decision_procedure.h>

#include <util/format_expr.h>

void path_symex_stept::output(std::ostream &out) const
{
  out << "PCs:";

/*
    for(pc_vectort::const_iterator p_it=s_it->pc_vector.begin();
        p_it!=pc_vector.end();
        p_it++)
      out << " " << *p_it;
 */
  out << "\n";

  out << "SSA Guard: " << format(ssa_guard) << "\n";
  out << "LHS: " << format(lhs) << "\n";
  out << "SSA LHS: " << format(ssa_lhs) << "\n";
  out << "SSA RHS: " << format(ssa_rhs) << "\n";
  out << "\n";
}

void path_symex_stept::convert(decision_proceduret &dest) const
{
  for(const auto &arg : function_arguments)
    dest << equal_exprt(arg.ssa_lhs, arg.ssa_rhs);

  if(ssa_rhs.is_not_nil())
    dest << equal_exprt(ssa_lhs, ssa_rhs);

  if(ssa_guard.is_not_nil())
    dest << ssa_guard;
}

void path_symex_step_reft::build_history(
  std::vector<path_symex_step_reft> &dest) const
{
  dest.clear();

  path_symex_step_reft s=*this;
  while(!s.is_nil())
  {
    dest.push_back(s);
    --s;
  }

  // the above goes backwards: now need to reverse
  std::reverse(dest.begin(), dest.end());
}
