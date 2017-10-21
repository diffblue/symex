/*******************************************************************\

Module: Shortest path graph

Author: elizabeth.polgreen@cs.ox.ac.uk

\*******************************************************************/

#include "shortest_path_graph.h"

#include <algorithm>

void shortest_path_grapht::get_path_lengths_in_function()
{
  bool found_property = false;
  bool found_end = false;
  node_indext end_index;
  node_indext property_index;
  node_indext index = 0;
  for(auto &n : nodes)
  {
    if(n.PC->is_assert())
    {
      if(found_property == false)
      {
        n.is_property = true;
        n.shortest_path_to_property = 0;
        found_property = true;
        property_index = index;
      }
      else
        throw "shortest path search cannot be used with multiple properties";
    }
    if(n.PC->is_end_function())
    {
      end_index = index;
      found_end = true;
    }
    index++;
  }

  if(!found_property)
  {
    nodes[end_index].shortest_path_to_property = 0;
    bfs(end_index);
  }
  else
    bfs(property_index);

  write_lengths_to_locs();
}

void per_function_shortest_patht::build(const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(it->second.body_available())
    {
      shortest_path_grapht path_graph(it->second.body, locs);
    }
}

void shortest_path_grapht::bfs(node_indext property_index)
{
  // does BFS, not Dijkstra
  // we hope the graph is sparse
  std::vector<node_indext> frontier_set;

  frontier_set.reserve(nodes.size());

  frontier_set.push_back(property_index);
  nodes[property_index].visited = true;

  for(std::size_t d = 1; !frontier_set.empty(); ++d)
  {
    std::vector<node_indext> new_frontier_set;

    for(const auto &node_index : frontier_set)
    {
      const nodet &n = nodes[node_index];

      // do all neighbors
      // we go backwards through the graph
      for(const auto &edge_in : n.in)
      {
        node_indext node_in = edge_in.first;

        if(!nodes[node_in].visited)
        {
          nodes[node_in].shortest_path_to_property = d;
          nodes[node_in].visited = true;
          new_frontier_set.push_back(node_in);
        }
      }
    }

    frontier_set.swap(new_frontier_set);
  }
}

void shortest_path_grapht::write_lengths_to_locs()
{
  for(const auto &n : nodes)
  {
    loc_reft l = target_to_loc_map[n.PC];
    locs.loc_vector[l.loc_number].distance_to_property
        = n.shortest_path_to_property;
  }
}

void shortest_path_grapht::get_path_lengths_to_property()
{
  node_indext property_index;
  bool found_property=false;
  for(node_indext n=0; n<nodes.size(); n++)
  {
    if(nodes[n].PC->is_assert())
    {
      if(found_property == false)
      {
        nodes[n].is_property = true;
        nodes[n].shortest_path_to_property = 0;
        working_set.insert(n);
        property_index = n;
        found_property = true;
      }
      else
        throw "shortest path search cannot be used for multiple properties";
    }
  }
  if(!found_property)
    throw "unable to find property";

  bfs(property_index);

  write_lengths_to_locs();
}


