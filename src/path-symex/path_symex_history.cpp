/*******************************************************************\

Module: History of path-based symbolic simulator

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// History of path-based symbolic simulator

#include "path_symex_history.h"

#include <algorithm>

#include <util/decision_procedure.h>

#include <langapi/language_util.h>

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

  if(is_branch())
    out << "SSA cond: " << from_expr(branch().ssa_cond) << "\n";

  if(is_assign())
  {
    const auto &a = assign();
    out << "LHS: " << from_expr(a.lhs) << "\n";
    out << "SSA LHS: " << from_expr(a.ssa_lhs) << "\n";
    out << "SSA RHS: " << from_expr(a.ssa_rhs) << "\n";
  }

  out << "\n";
}

void path_symex_stept::convert(decision_proceduret &dest) const
{
  if(is_call())
  {
    for(const auto &arg : call().function_arguments)
      dest << equal_exprt(arg.ssa_lhs, arg.ssa_rhs);
  }
  else if(is_assign())
  {
    const auto &a = assign();
    if(a.ssa_rhs.is_not_nil())
      dest << equal_exprt(a.ssa_lhs, a.ssa_rhs);
  }
  else if(is_branch())
    dest << branch().ssa_cond;
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
