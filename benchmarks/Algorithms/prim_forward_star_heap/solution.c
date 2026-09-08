#include "Data_structures/priority_queue_decrease_key/priority_queue_decrease_key_def.h"

#define MAX_PRIORITY_QUEUE_SIZE 100000
#define INF 1000000000

struct mst_tree {
	int* u;
	int* v;
	int* wt;
};

int* malloc_int_array(int n)

;

struct mst_tree* malloc_mst_tree()

;

struct mst_tree* prim_forward_star_heap(int* from_arr, int* to_arr,
										int* weight_arr, int n, int m)

{
	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_wt = malloc_int_array(n - 1);

	int* from_new = malloc_int_array(2 * m);
	int* to_new = malloc_int_array(2 * m);
	int* weight_new = malloc_int_array(2 * m);

	{
	int i = 0;

	for (; i < m; i++) {
		from_new[2 * i] = from_arr[i];
		to_new[2 * i] = to_arr[i];
		weight_new[2 * i] = weight_arr[i];

		from_new[2 * i + 1] = to_arr[i];
		to_new[2 * i + 1] = from_arr[i];
		weight_new[2 * i + 1] = weight_arr[i];
	}
	}

	int* first = malloc_int_array(n);
	int* link = malloc_int_array(2 * m);

	{
	int i = 0;

	for (; i < n; i++) {
		first[i] = -1;
	}
	}

	{
	int i = 0;

	for (; i < 2 * m; i++) {
		link[i] = -1;
	}
	}

	{
	int i = 0;

			for (; i < 2 * m; i++) {
				int u = from_new[i];

				int tmp = first[u];
				first[u] = i;
				link[i] = tmp;
			}
	}

	int* visited = malloc_int_array(n);
	int* lowcost = malloc_int_array(n);
	int* edge_parent = malloc_int_array(n);

	{
	int i = 0;

	for (; i < n; i++) {
		visited[i] = 0;
		lowcost[i] = 1000000000;
		edge_parent[i] = -1;
	}

		}

		int heap_capacity = 2 * m + 2;
		int* heap_cost = malloc_int_array(heap_capacity);
		int* heap_vertex = malloc_int_array(heap_capacity);
		int* heap_pos = malloc_int_array(n);
		int heap_size = 0;

		{
			int pos_i = 0;

			for (; pos_i < n; pos_i++) {
				heap_pos[pos_i] = -1;
			}
		}

		lowcost[0] = 0;

		pqdk_push(heap_cost, heap_vertex, heap_pos, &heap_size, n, 0, 0)
			;

		int chosen = 0;

		while (heap_size > 0 && chosen < n) {
			int minIndex;
			int min;

			pqdk_pop(heap_cost, heap_vertex, heap_pos, &heap_size, n, &minIndex, &min)
				;

			visited[minIndex] = 1;
			chosen++;
			int cur_edge = first[minIndex];

			while (cur_edge != -1) {
				if (0 <= cur_edge && cur_edge < 2 * m) {
					int to_node = to_new[cur_edge];
					int edge_weight = weight_new[cur_edge];
					if (0 <= to_node && to_node < n && visited[to_node] == 0 && edge_weight < lowcost[to_node]) {
						lowcost[to_node] = edge_weight;
						edge_parent[to_node] = cur_edge;

						pqdk_update_or_push(heap_cost, heap_vertex, heap_pos, &heap_size, n, to_node, edge_weight)
							;

					}
					cur_edge = link[cur_edge];
				} else {
					cur_edge = -1;
				}
			}

		}

			int out_i = 1;
		int mst_idx = 0;

		for (; out_i < n; out_i++) {

			int edge_id = edge_parent[out_i];
			if (edge_id == -1) continue;
			if (0 <= edge_id && edge_id < 2 * m && mst_idx < n - 1) {

				out_u[mst_idx] = from_new[edge_id];
				out_v[mst_idx] = to_new[edge_id];
				out_wt[mst_idx] = weight_new[edge_id];
				mst_idx++;
			}
		}

		struct mst_tree* p = malloc_mst_tree();
	p->u = out_u;
	p->v = out_v;
	p->wt = out_wt;
	return p;
}
