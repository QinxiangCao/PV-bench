#include "Data_structures/priority_queue_index/priority_queue_index_def.h"

/*@ Import Coq From GraphLib Require Import Zweight */
/*@ Import Coq Require Import PVbench.Algorithms.Dijkstra_linked_forward_star_index_queue.rocq.spec_lib */
/*@ Import Coq Import DijkstraGraph */
/*@ Import Coq Import DijkstraLinkedForwardStar */
/*@ Import Coq Import DijkstraIndexQueue */
/*@ Extern Coq (G :: *) */
/*@ Extern Coq (state :: *) */
/*@ Extern Coq
      (dijkstra_init_dist : Z -> Z -> list Z -> Prop)
      (dijkstra_shortest_dist : G -> Z -> list Z -> Prop)
      (nonnegative_edges : G -> Prop)
      (shortest_path_relaxation_bounded : G -> Z -> Z -> Prop)
      (dist_init_loop : Z -> list Z -> Prop)
	      (graph_state_model : G -> (Z -> Prop) -> list Z -> state -> Prop)
	      (visited_set_empty : (Z -> Prop) -> Prop)
	      (visited_set_add : (Z -> Prop) -> Z -> (Z -> Prop) -> Prop)
	      (dijkstra_heap_lfs_initial_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (unit -> state -> Prop) -> Prop)
      (vector_shape : list Z -> Prop)
      (graph_has_size : G -> Z -> Prop)
      (vertex_valid : G -> Z -> Prop)
      (forward_star_model :
        G -> Z -> list Z -> list Z -> list Z -> list Z -> Prop)
      (storage_index : Z -> Prop)
      (GraphForwardStar::store_graph :
        G -> Z -> Z -> Z -> Z -> Z -> Assertion)
	      (index_queue_push_result :
	        multiset (Z * Z) -> multiset (Z * Z) -> Z -> Z -> Prop)
	      (index_queue_pop_result :
	        multiset (Z * Z) -> multiset (Z * Z) -> Z -> Z -> Prop)
	      (dijkstra_heap_loop_state :
	        G -> Z -> (Z -> Prop) -> list Z -> multiset (Z * Z) -> Prop)
	      (dijkstra_heap_edge_loop_state :
	        G -> Z -> (Z -> Prop) -> Z -> Z -> Z ->
	        list Z -> multiset (Z * Z) -> Prop)
	      (dijkstra_heap_loop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_heap_after_pop_refines :
	        G -> Z -> list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) -> Z -> Z ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_heap_edge_loop_refines :
	        G -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
	      (dijkstra_heap_after_relax_refines :
	        G -> Z -> Z -> Z -> Z -> Z -> Z ->
	        list Z -> list Z -> list Z -> list Z ->
	        (Z -> Prop) -> list Z -> multiset (Z * Z) ->
	        (unit -> state -> Prop) -> Prop)
 */

#define MAX_VERTEX_COUNT 10
#define INF 1000000000
#define MAX_PRIORITY_QUEUE_SIZE 100000

void dijkstra_linked_forward_star_init(int vertex_count, int source, int *dist)

{

	  for (int i = 0; i < MAX_VERTEX_COUNT; ++i) {
    dist[i] = INF;
  }

  dist[source] = 0;
}

void dijkstra_linked_forward_star_index_queue(int vertex_count, int source, int edge_count,
	                                  int *head, int *to, int *weight, int *next,
	                                  int *dist)
/*@ With (g : G) (dist0 : list Z)
    Require
      graph_has_size(g, vertex_count) &&
      vertex_valid(g, source) &&
      nonnegative_edges(g) &&
      shortest_path_relaxation_bounded(g, source, INF) &&
      0 < heap_capacity &&
      MAX_PRIORITY_QUEUE_SIZE <= heap_capacity &&
      edge_count + 1 <= heap_capacity &&
      0 <= edge_count && edge_count <= MAX_PRIORITY_QUEUE_SIZE &&
	      vector_shape(dist0) &&
	      GraphForwardStar::store_graph(g, edge_count, head, to, weight, next) *
	      IntArray::full(dist, MAX_VERTEX_COUNT, dist0)
	    Ensure
	      exists dist_out,
	        dijkstra_shortest_dist(g, source, dist_out) &&
	        GraphForwardStar::store_graph(g, edge_count, head, to, weight, next) *
	        IntArray::full(dist, MAX_VERTEX_COUNT, dist_out)
	 */
{
  dijkstra_linked_forward_star_init(vertex_count, source, dist);
  int queue_key[MAX_PRIORITY_QUEUE_SIZE];
  int queue_data[MAX_PRIORITY_QUEUE_SIZE];

  int queue_size = 0;

  push(queue_key, queue_data, queue_size, source, 0)
    ;
  queue_size = queue_size + 1;

  while (queue_size != 0) {
    int cur_vertex;
    int cur_distance;

    pop(queue_key, queue_data, queue_size, &cur_vertex, &cur_distance)
      ;
    queue_size = queue_size - 1;

    if (cur_distance == dist[cur_vertex]) {

      for (int edge = head[cur_vertex]; edge != -1; edge = next[edge]) {
        int neighbor = to[edge];
        int edge_weight = weight[edge];

        if (edge_weight >= 0 && cur_distance <= INF - edge_weight) {
          int candidate = cur_distance + edge_weight;

          if (candidate < dist[neighbor]) {
            dist[neighbor] = candidate;

	            push(queue_key, queue_data, queue_size, neighbor, candidate)
	              ;
	            queue_size = queue_size + 1;
		    }
		  }
		}
	    }
	  }

	}
