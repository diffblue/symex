/*******************************************************************\

Module: Path-based Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Path-based Symbolic Execution

#ifndef CPROVER_SYMEX_PATH_SEARCH_H
#define CPROVER_SYMEX_PATH_SEARCH_H

#define OPT_PATH_SEARCH                                                        \
  "(depth):(context-bound):(branch-bound):(unwind):(unwinding-assertions)" \
  "(max-search-time):(bfs)(dfs)(locs)(cover):(eager-infeasibility)(stop-on-fail)"

#define HELP_PATH_SEARCH \
  " --depth N                    limit the depth to N\n" \
  " --context-bound N            limit the number of thread context switches\n" \
  " --branch-bound N             limit the number of branches\n" \
  " --unwind N                   limit the number of unwinding\n" \
  " --unwinding-assertions       unwinding assertions\n" \
  " --max-search-time N          set a time limit\n" \
  " --bfs                        use breadth first search heuristic\n" \
  " --dfs                        use depth first search heuristic\n" \
  " --locs                       use locs heuristic\n" \
  " --eager-infeasability        eager infeasiblity\n" \
  " --stop-on-fail               stop on fail\n" \
  " --show-trace                 show the trace\n" \
  " --cover CC                   create test-suite with coverage criterion CC\n"

#include <chrono>

#include <util/expanding_vector.h>

#include <goto-programs/safety_checker.h>

#include "../path-symex/path_symex_state.h"

#include <limits>

class path_searcht:public safety_checkert
{
public:
  explicit path_searcht(const namespacet &_ns):
    safety_checkert(_ns),
    show_vcc(false),
    eager_infeasibility(false),
    stop_on_fail(false),
    unwinding_assertions(false),
    number_of_dropped_states(0),
    number_of_paths(0),
    number_of_steps(0),
    number_of_feasible_paths(0),
    number_of_infeasible_paths(0),
    number_of_VCCs(0),
    number_of_VCCs_after_simplification(0),
    number_of_failed_properties(0),
    number_of_locs(0),
    depth_limit(std::numeric_limits<unsigned>::max()),
    context_bound(std::numeric_limits<unsigned>::max()),
    branch_bound(std::numeric_limits<unsigned>::max()),
    unwind_limit(std::numeric_limits<unsigned>::max()),
    time_limit(std::numeric_limits<unsigned>::max()),
    search_heuristic(search_heuristict::DFS)
  {
  }

  virtual resultt operator()(
    const goto_functionst &goto_functions);

  void set_depth_limit(int limit)
  {
    depth_limit=limit;
  }

  void set_context_bound(int limit)
  {
    context_bound=limit;
  }

  void set_branch_bound(int limit)
  {
    branch_bound=limit;
  }

  void set_unwind_limit(int limit)
  {
    unwind_limit=limit;
  }

  void set_time_limit(int limit)
  {
    time_limit=limit;
  }

  bool show_vcc;
  bool eager_infeasibility;
  bool stop_on_fail;
  bool unwinding_assertions;

  // statistics
  std::size_t number_of_dropped_states;
  std::size_t number_of_paths;
  std::size_t number_of_steps;
  std::size_t number_of_feasible_paths;
  std::size_t number_of_infeasible_paths;
  std::size_t number_of_VCCs;
  std::size_t number_of_VCCs_after_simplification;
  std::size_t number_of_failed_properties;
  std::size_t number_of_locs;

  std::chrono::time_point<std::chrono::steady_clock> start_time;
  std::chrono::duration<double> solver_time;

  enum statust { NOT_REACHED, SUCCESS, FAILURE };

  struct property_entryt
  {
    statust status;
    irep_idt description;
    goto_tracet error_trace;
    source_locationt source_location;

    bool is_success() const { return status==SUCCESS; }
    bool is_failure() const { return status==FAILURE; }
    bool is_not_reached() const { return status==NOT_REACHED; }
  };

  void set_dfs() { search_heuristic=search_heuristict::DFS; }
  void set_bfs() { search_heuristic=search_heuristict::BFS; }
  void set_locs() { search_heuristic=search_heuristict::LOCS; }

  void set_unwinding_assertions(bool _unwinding_assertions)
  {
    unwinding_assertions=_unwinding_assertions;
  }

  typedef std::map<irep_idt, property_entryt> property_mapt;
  property_mapt property_map;

protected:
  typedef path_symex_statet statet;

  // State queue. Iterators are stable.
  // The states most recently executed are at the head.
  typedef std::list<statet> queuet;
  queuet queue;

  // search heuristic
  void pick_state();

  struct loc_datat
  {
    bool visited;
    loc_datat():visited(false) { }
  };

  expanding_vectort<loc_datat> loc_data;

  bool execute(queuet::iterator state);
  void check_assertion(statet &);
  bool is_feasible(const statet &);
  void do_show_vcc(statet &);
  bool drop_state(const statet &);
  void report_statistics();
  void initialize_property_map(const goto_functionst &);

  unsigned depth_limit;
  unsigned context_bound;
  unsigned branch_bound;
  unsigned unwind_limit;
  unsigned time_limit;

  enum class search_heuristict { DFS, BFS, LOCS } search_heuristic;

  source_locationt last_source_location;
};

void parse_path_search_options(
  path_searcht &path_search,
  const class cmdlinet &cmdline);

#endif // CPROVER_SYMEX_PATH_SEARCH_H
