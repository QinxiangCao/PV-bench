#include "Data_structures/priority_queue_decrease_key/rocq/priority_queue_decrease_key_def.h"

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

void dijkstra_linked_forward_star_decrease_key(int vertex_count, int source, int edge_count,
                                  int *head, int *to, int *weight, int *next,
                                  int *dist)

{
  dijkstra_linked_forward_star_init(vertex_count, source, dist);
  int queue_key[MAX_PRIORITY_QUEUE_SIZE];
  int queue_data[MAX_PRIORITY_QUEUE_SIZE];
  int queue_pos[MAX_VERTEX_COUNT];

  for (int i = 0; i < MAX_VERTEX_COUNT; ++i) {
    queue_pos[i] = -1;
  }

  int queue_size = 0;

  pqdk_push(queue_key, queue_data, queue_pos, &queue_size, MAX_VERTEX_COUNT, source, 0)
    ;

  while (queue_size != 0) {
    int cur_vertex;
    int cur_distance;

    pqdk_pop(queue_key, queue_data, queue_pos, &queue_size, MAX_VERTEX_COUNT, &cur_vertex, &cur_distance)
      ;

  for (int edge = head[cur_vertex]; edge != -1; edge = next[edge]) {
    int neighbor = to[edge];
    int edge_weight = weight[edge];

    if (edge_weight >= 0 && cur_distance <= INF - edge_weight) {
      int candidate = cur_distance + edge_weight;

      if (candidate < dist[neighbor]) {
        dist[neighbor] = candidate;

        pqdk_update_or_push(queue_key, queue_data, queue_pos, &queue_size, MAX_VERTEX_COUNT, neighbor, candidate)
          ;
      }
    }
  }
  }

}
