#include "Data_structures/priority_queue_index/rocq/priority_queue_index_def.h"

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
