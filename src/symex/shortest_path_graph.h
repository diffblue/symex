/*******************************************************************\

Module: Shortest path graph

Author: elizabeth.polgreen@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_SYMEX_SHORTEST_PATH_GRAPH_H
#define CPROVER_SYMEX_SHORTEST_PATH_GRAPH_H

#include <goto-programs/cfg.h>
#include <path-symex/locs.h>
#include <goto-programs/goto_model.h>
#include <limits>


struct shortest_path_nodet
{
  bool visited;
  std::size_t shortest_path_to_property;
  bool is_property;
  shortest_path_nodet():
    visited(false),
    is_property(false)
  {
    shortest_path_to_property = std::numeric_limits<std::size_t>::max();
  }
};

/// \brief constructs a CFG of all program locations. Then computes
/// the shortest path from every program location to a single property.
/// WARNING: if more than one property is present in the graph, we will
/// use the first property found
/// The distances computed for each node are written to the corresponding
/// loct in the locst passed as param to the constructor. This allows us
/// to use these numbers to guide a symex search
/// \param goto functions to create the CFG from, locs struct made from the
/// same goto_functions
class shortest_path_grapht: public cfg_baset<shortest_path_nodet>
{
public:
  explicit shortest_path_grapht(
      const goto_functionst &_goto_functions, locst &_locs):
    locs(_locs),
    target_to_loc_map(_locs)
    {
    cfg_baset<shortest_path_nodet>::operator()(_goto_functions);
    get_path_lengths_to_property();
    }

  explicit shortest_path_grapht(
      const goto_programt &_goto_program, locst &_locs):
    locs(_locs),
    target_to_loc_map(_locs)
    {
    cfg_baset<shortest_path_nodet>::operator()(_goto_program);
    get_path_lengths_in_function();
    }

protected:
  /// \brief writes the computed shortest path for every node
  /// in the graph to the corresponding location in locst.
  /// This is done so that we can use these numbers to guide
  /// a search heuristic for symex
  void write_lengths_to_locs();
  /// \brief computes the shortest path from every node in
  /// the graph to a single property. WARNING: if more than one property
  /// is present, we use the first one discovered.
  /// Calls bfs() to do this.
  void get_path_lengths_to_property();
  /// \brief computes the shortest path from every node in a
  /// graph to the property, or the end of the funciton if
  /// there is no property.
  /// we assume the graph is a graph of a single function.
  void get_path_lengths_in_function();
  /// \brief implements backwards BFS to compute distance from every node in
  /// the graph to the node index given as parameter
  /// \param destination node index
  void bfs(node_indext property_index);
  std::set<node_indext> working_set;
  locst &locs;
  target_to_loc_mapt target_to_loc_map;
};

/// \brief class contains CFG of program locations
/// for every function with the shortest distance to a
/// property, or the end of a function, calculated for each location
/// The distances computed for each node are written to the corresponding
/// loct in the locst passed as param to the constructor. This allows us
/// to use these numbers to guide a symex search
/// \param goto functions to create the CFGs from, locs struct made from the
/// same goto_functions
class per_function_shortest_patht
{
public:
  explicit per_function_shortest_patht(
      const goto_functionst &_goto_functions, locst &_locs):
  locs(_locs)
  {
    build(_goto_functions);
  }

protected:
  locst &locs;
  void build(const goto_functionst & goto_functions);
};

#endif /* CPROVER_SYMEX_SHORTEST_PATH_GRAPH_H */
