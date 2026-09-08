struct mst_tree {
	int* u;
	int* v;
	int* wt;
};

int* malloc_int_array(int n)

;

struct mst_tree* malloc_mst_tree()

;

struct mst_tree* prim(int* from_arr, int* to_arr, int* weight_arr, int n, int m)

{
	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_wt = malloc_int_array(n - 1);

    int* from_new = malloc_int_array(2*m);
    int* to_new = malloc_int_array(2*m);
    int* weight_new = malloc_int_array(2*m);
		int i = 0;

	    for (; i < m; i++) {
        from_new[2*i] = from_arr[i];
        to_new[2*i] = to_arr[i];
        weight_new[2*i] = weight_arr[i];

        from_new[2*i + 1] = to_arr[i];
        to_new[2*i + 1] = from_arr[i];
        weight_new[2*i + 1] = weight_arr[i];
    }

		int* first = malloc_int_array(n);
		int* link = malloc_int_array(2 * m);
		 i = 0;

	for (; i < n; i++) {
		first[i] = -1;
	}

	i = 0;

		for (; i < 2 * m; i++) {
			link[i] = -1;
		}

		i = 0;

		for (; i < 2 * m; i++) {
			int u = from_new[i];

			int tmp = first[u];
			first[u] = i;
			link[i] = tmp;
		}

	int* visited = malloc_int_array(n);
		int* lowcost = malloc_int_array(n);
		int* edge_parent = malloc_int_array(n);
		i = 0;

			for (; i < n; i++) {
				lowcost[i] = 1000000000;
				visited[i] = 0;
			edge_parent[i] = -1;
		}

		lowcost[0] = 0;
		i = 0;

					for (; i < n; i++) {
						int min = 1000000000;
						int minIndex = -1;
					int j =0;

					for (; j < n; j++) {
					if (visited[j] == 0) {
						if (lowcost[j] < min) {
							min = lowcost[j];
							minIndex = j;
						}
					}
				    }

					if (minIndex != -1) {
						visited[minIndex] = 1;

							int cur_edge = first[minIndex];

						while (cur_edge != -1) {
								if (0 <= cur_edge && cur_edge < 2 * m) {
										int to_node = to_new[cur_edge];
										int edge_weight = weight_new[cur_edge];

													if (0 <= to_node && to_node < n && visited[to_node] == 0 && edge_weight < lowcost[to_node])
											 {
									lowcost[to_node] = edge_weight;
									edge_parent[to_node] = cur_edge;
												}

								cur_edge = link[cur_edge];

					} else {
						cur_edge = -1;
					}
				}

			}
	}

	i = 1;
	int mst_idx = 0;

	for (; i < n; i++) {
		if (edge_parent[i] == -1) continue;
		int edge_id = edge_parent[i];
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
