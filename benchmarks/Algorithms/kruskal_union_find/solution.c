#include "Data_structures/union_find/union_find_def.h"

int* malloc_int_array(int n)

;

void free_int_array(int* a)

;

struct mst_tree {
	int* ru;
	int* rv;
	int* rw;
};

struct mst_tree* malloc_mst_tree()

;

void swap_int(int* a, int* b)

{
	int t = *a;
	*a = *b;
	*b = t;
}

void swap_edge(int* u, int* v, int* w, int i, int j)

{
	if (i != j) {
		if (i < j) {

			swap_int(&u[i], &u[j]) ;
			swap_int(&v[i], &v[j]) ;
			swap_int(&w[i], &w[j]) ;
		} else {

			swap_int(&u[i], &u[j]) ;
			swap_int(&v[i], &v[j]) ;
			swap_int(&w[i], &w[j]) ;
		}
	}
}

int partitionByWeight(int* u, int* v, int* w, int left, int right)

{
	int pivot_w = w[right];
	int i = left;

	for (int j = left; j < right; j++) {
		if (w[j] < pivot_w) {
			swap_edge(u, v, w, i, j)
				;
			i++;
		}
	}

	swap_edge(u, v, w, i, right)
		;
	return i;
}

void quickByWeightRange(int* u, int* v, int* w, int left, int right)

{
	if (left < right) {
		int pivot = partitionByWeight(u, v, w, left, right);
		quickByWeightRange(u, v, w, left, pivot - 1);
		quickByWeightRange(u, v, w, pivot + 1, right);
	}
}

void quickByWeight(int* u, int* v, int* w, int n)

{
	if (n > 0) {
		quickByWeightRange(u, v, w, 0, n - 1);
	}
}

struct mst_tree* kruskal(int*u, int* v, int* w, int n, int m)

{
	quickByWeight(u, v, w, m)
		;

	struct union_find* uf = uf_create(n);

	int* out_u = malloc_int_array(n - 1);
	int* out_v = malloc_int_array(n - 1);
	int* out_w = malloc_int_array(n - 1);

	int chosen = 0;
	int i = 0;

	for (; i < m && chosen < n - 1; i++) {
		int edge_u = u[i];
		int edge_v = v[i];
		int edge_w = w[i];

		int root_u = uf_find(uf, edge_u)
			;

		int root_v = uf_find(uf, edge_v)
			;

		if (root_u != root_v) {
			out_u[chosen] = edge_u;
			out_v[chosen] = edge_v;
			out_w[chosen] = edge_w;
			chosen++;
			uf_union(uf, edge_u, edge_v)
				;

		} else {

		}

		}

	uf_free(uf) ;

	struct mst_tree* result = malloc_mst_tree();
	result->ru = out_u;
	result->rv = out_v;
	result->rw = out_w;
	return result;

}
