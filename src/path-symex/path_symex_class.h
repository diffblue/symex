/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Concrete Symbolic Transformer

#ifndef CPROVER_PATH_SYMEX_PATH_SYMEX_CLASS_H
#define CPROVER_PATH_SYMEX_PATH_SYMEX_CLASS_H

#include "path_symex.h"

class path_symext
{
public:
  path_symext()
  {
  }

  virtual void operator()(
    path_symex_statet &state,
    std::list<path_symex_statet> &furter_states);

  virtual void operator()(path_symex_statet &state);

  void do_goto(
    path_symex_statet &state,
    bool taken);

  virtual void do_assert_fail(path_symex_statet &state)
  {
    const goto_programt::instructiont &instruction=
      *state.get_instruction();

    state.record_step();
    state.next_pc();
    exprt ssa_guard=state.read(not_exprt(instruction.get_condition()));
    state.history->ssa_guard=ssa_guard;
  }

  typedef path_symex_stept stept;

protected:
  void do_goto(
    path_symex_statet &state,
    std::list<path_symex_statet> &further_states);

  void function_call(
    path_symex_statet &state,
    const code_function_callt &call,
    std::list<path_symex_statet> &further_states)
  {
    exprt f=state.read(call.function());
    function_call_rec(state, call, f, further_states);
  }

  void function_call_rec(
    path_symex_statet &,
    const code_function_callt &,
    const exprt &function,
    std::list<path_symex_statet> &further_states);

  void function_call_symbol(
    path_symex_statet &,
    const code_function_callt &,
    const symbol_exprt &function,
    std::list<path_symex_statet> &further_states);

  void return_from_function(path_symex_statet &state);

  void set_return_value(path_symex_statet &, const exprt &);

  void symex_allocate(
    path_symex_statet &state,
    const exprt &lhs,
    const side_effect_exprt &code);

  void symex_new(
    path_symex_statet &state,
    const exprt &lhs,
    const side_effect_exprt &code);

  void symex_va_arg_next(
    path_symex_statet &state,
    const exprt &lhs,
    const side_effect_exprt &code);

  void assign(
    path_symex_statet &state,
    const exprt &lhs,
    const exprt &rhs);

  void assign(
    path_symex_statet &state,
    const code_assignt &assignment)
  {
    assign(state, assignment.lhs(), assignment.rhs());
  }

  void assign_rec(
    path_symex_statet &state,
    exprt::operandst &guard, // SSAed
    const exprt &ssa_lhs, // SSAed, recursion here
    const exprt &ssa_rhs); // SSAed

  void assign_rec_symbol(
    path_symex_statet &state,
    exprt::operandst &guard, // SSAed
    const symbol_exprt &ssa_lhs, // SSAed, recursion here
    const exprt &ssa_rhs); // SSAed

  void assign_rec_member(
    path_symex_statet &state,
    exprt::operandst &guard, // SSAed
    const member_exprt &ssa_lhs, // SSAed, recursion here
    const exprt &ssa_rhs); // SSAed

  void assign_rec_index(
    path_symex_statet &state,
    exprt::operandst &guard, // SSAed
    const index_exprt &ssa_lhs, // SSAed, recursion here
    const exprt &ssa_rhs); // SSAed

  static bool propagate(const exprt &src);
};


#endif // CPROVER_PATH_SYMEX_PATH_SYMEX_CLASS_H
