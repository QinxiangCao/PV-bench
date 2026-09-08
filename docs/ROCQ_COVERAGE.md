# PV-Bench Rocq Coverage

The Rocq (Coq/QCP) version of PV-Bench provides formal specifications, program annotations and
generated verification goals for C program verification, covering classic algorithms, Codeforces
problems, data structures and engineering code.

The `main` branch carries **215 Rocq cases**: 74 algorithms, 128 Codeforces problems, 5 data structures and 8 engineering cases. Codeforces ratings range from **800 to 2800**.

Each case's Rocq files live in a `rocq/` directory next to `lean/`: `solution_spec.c` with the
function contract, `solution_annotated.c` with the verification annotations, the specification
library `spec_lib.v` and — where needed — the helper library `helper_lib.v`. QCP-generated goals
and proofs (`*_goal.v`, `*_proof_auto.v`, `*_proof_manual.v`) go under `groundtruth/`, which is
built locally and not committed. For dependency configuration and build instructions see the
[README](README.md).

## Composition

| Category | Cases | Content |
| --- | --- | --- |
| Algorithms (`Algorithms/`) | 74 | sorting, number theory, dynamic programming, greedy methods, sequence processing, graph algorithms and computational geometry |
| Competitive problems (`Codeforces/`) | 128 | constructive, math, string, game, graph and optimization problems |
| Data structures (`Data_structures/`) | 5 | array stack, binary indexed tree and three priority-queue interfaces |
| Engineering (`Engineering/`) | 8 | MiniSat dynamic vectors and C string / memory routines |
| Total | 215 | |

Cases are counted per independent implementation. Different implementations of the same algorithm
are counted separately — for example five quicksort partition schemes, four Prim implementations
and three depth-first searches.

## Shared components and cross-case dependencies

Some algorithm cases do not implement their own container: they reuse a data-structure case from
this benchmark, including its C definitions and its Rocq specification. Verifying such a case
therefore requires the data-structure case as well — the two are not independent.

| Case | Reuses |
| --- | --- |
| [Dijkstra_linked_forward_star_decrease_key](../benchmarks/Algorithms/Dijkstra_linked_forward_star_decrease_key/rocq/) | [priority_queue_decrease_key](../benchmarks/Data_structures/priority_queue_decrease_key/rocq/) |
| [Dijkstra_linked_forward_star_index_queue](../benchmarks/Algorithms/Dijkstra_linked_forward_star_index_queue/rocq/) | [priority_queue_index](../benchmarks/Data_structures/priority_queue_index/rocq/) |
| [prim_forward_star_heap](../benchmarks/Algorithms/prim_forward_star_heap/rocq/) | [priority_queue_decrease_key](../benchmarks/Data_structures/priority_queue_decrease_key/rocq/) |
| [kruskal_union_find](../benchmarks/Algorithms/kruskal_union_find/rocq/) | `Data_structures/union_find` — **not part of this repository yet**; the header is included from the QCP example tree |

Beyond these, many cases include shared C definitions that come with QCP rather than with this
repository (`QCP_examples/QCP_demos_LLM/` and `QCP_examples/stdlib/`): `string.h` (29 cases),
`array2_ext_def.h` (24), `safeexec_def.h` (14), `array2_def.h` (14), `graph_matrix_def.h` (12),
`int_ptr_array2_def.h` (8) and `sll_def.h` (3). They provide array, matrix, list, string and
monadic-execution representations, and must be on the include path for a case to be checked.

## Algorithms (74)

| Primary category | Cases |
| --- | --- |
| Sorting and discretization | 12 |
| Number theory and modular arithmetic | 11 |
| Dynamic programming | 22 |
| Greedy, binary search and two pointers | 7 |
| Sequences, strings and range queries | 6 |
| Computational geometry | 2 |
| Graph algorithms | 14 |

### Sorting and discretization (12)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Bubble sort | [bubble_sort](../benchmarks/Algorithms/bubble_sort/rocq/) | adjacent swaps and a sorted suffix |
| Decimal radix sort | [bucket_sort](../benchmarks/Algorithms/bucket_sort/rocq/) | stable bucketing by decimal digit |
| Stable counting sort | [counting_sort](../benchmarks/Algorithms/counting_sort/rocq/) | frequencies, prefix sums and stable placement |
| Coordinate discretization | [discretize](../benchmarks/Algorithms/discretize/rocq/) | sorting, deduplication and an order-preserving map |
| Insertion sort | [insertion_sort](../benchmarks/Algorithms/insertion_sort/rocq/) | sorted prefix and element insertion |
| Bidirectional selection sort | [optimized_selection_sort](../benchmarks/Algorithms/optimized_selection_sort/rocq/) | picks the minimum and the maximum each round |
| Quicksort: Hoare fill partition | [quicksort_hoare_fill_index](../benchmarks/Algorithms/quicksort_hoare_fill_index/rocq/) | fill-hole partition |
| Quicksort: Hoare fill partition, variant 2 | [quicksort_hoare_fill_index2](../benchmarks/Algorithms/quicksort_hoare_fill_index2/rocq/) | another fill-hole implementation |
| Quicksort: Hoare swap partition | [quicksort_hoare_swap_index](../benchmarks/Algorithms/quicksort_hoare_swap_index/rocq/) | two-way scan and swap |
| Quicksort: Hoare swap partition, variant 2 | [quicksort_hoare_swap_index2](../benchmarks/Algorithms/quicksort_hoare_swap_index2/rocq/) | another swap-partition implementation |
| Quicksort: Lomuto partition | [quicksort_lomuto_index](../benchmarks/Algorithms/quicksort_lomuto_index/rocq/) | scanning partition placing the pivot |
| Selection sort | [selection_sort](../benchmarks/Algorithms/selection_sort/rocq/) | picks the minimum each round |

### Number theory and modular arithmetic (11)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Chinese remainder theorem | [chinese_remainder_theorem](../benchmarks/Algorithms/chinese_remainder_theorem/rocq/) | congruence system with pairwise coprime moduli; P1495 |
| Inverse via Euler's theorem | [euler_theorem_inverse](../benchmarks/Algorithms/euler_theorem_inverse/rocq/) | coprimality, Euler's totient and modular power |
| Extended Chinese remainder theorem | [extended_chinese_remainder_theorem](../benchmarks/Algorithms/extended_chinese_remainder_theorem/rocq/) | consistent congruence system with non-coprime moduli; P4777 |
| Prime factorization | [integer_divide](../benchmarks/Algorithms/integer_divide/rocq/) | prime factors with multiplicity in non-decreasing order |
| Batch modular inverses | [linear_modular_inverse](../benchmarks/Algorithms/linear_modular_inverse/rocq/) | linear recurrence for a prime modulus; P3811 |
| Lucas' theorem | [lucas_theorem](../benchmarks/Algorithms/lucas_theorem/rocq/) | binomial coefficients modulo a prime; P3807 |
| Modular inverse | [modular_inverse](../benchmarks/Algorithms/modular_inverse/rocq/) | calls the extended Euclidean interface and normalizes the residue |
| Modular multiplication | [modular_mul](../benchmarks/Algorithms/modular_mul/rocq/) | doubling-and-adding to avoid overflow of a direct product |
| Fast modular exponentiation | [modular_power](../benchmarks/Algorithms/modular_power/rocq/) | binary exponentiation; P1226 |
| Sieve of Eratosthenes | [sieve_of_eratosthenes](../benchmarks/Algorithms/sieve_of_eratosthenes/rocq/) | prime and composite marking |
| Euler's linear sieve | [sieve_of_euler](../benchmarks/Algorithms/sieve_of_euler/rocq/) | prime enumeration and composite marking |

### Dynamic programming (22)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Annoying math homework | [annoying_math_homework](../benchmarks/Algorithms/annoying_math_homework/rocq/) | digit-sum counting over a range / digit DP; P4999 |
| Catalan numbers / stack sequences | [catalan_numbers](../benchmarks/Algorithms/catalan_numbers/rocq/) | counting valid pop sequences; P1044 |
| Choir formation | [choir_singing](../benchmarks/Algorithms/choir_singing/rocq/) | bidirectional longest increasing subsequence; P1091 |
| Climbing stairs | [climbing_stairs](../benchmarks/Algorithms/climbing_stairs/rocq/) | linear recurrence; LeetCode 70 |
| Largest reachable amount under a bound | [coin_change](../benchmarks/Algorithms/coin_change/rocq/) | denominations reused freely, maximizing within a bound |
| Largest concatenated number: subset DP | [concatenating_numbers_dp](../benchmarks/Algorithms/concatenating_numbers_dp/rocq/) | bitmask state, optimal first choice and concatenated output; P1012 |
| Energy necklace | [energy_necklace](../benchmarks/Algorithms/energy_necklace/rocq/) | circular interval DP maximizing merged energy; P1063 |
| House robber | [house_robber](../benchmarks/Algorithms/house_robber/rocq/) | adjacent-exclusive selection; LeetCode 198 |
| Longest common subsequence | [lcs_n](../benchmarks/Algorithms/lcs_n/rocq/) | two-dimensional DP |
| Longest increasing subsequence | [longest_increasing_subsequence](../benchmarks/Algorithms/longest_increasing_subsequence/rocq/) | per-position optimal substructure; LeetCode 300 |
| Longest non-decreasing subsequence | [longest_nondecreasing_subsequence](../benchmarks/Algorithms/longest_nondecreasing_subsequence/rocq/) | variant allowing equal neighbours |
| Matrix chain multiplication | [matrix_chain_multiplication](../benchmarks/Algorithms/matrix_chain_multiplication/rocq/) | interval DP and optimal parenthesization |
| Maximum-sum increasing subsequence | [max_sum_increasing_sequence](../benchmarks/Algorithms/max_sum_increasing_sequence/rocq/) | increasing subsequence optimized for sum |
| Maximum subarray sum | [maximum_subarray](../benchmarks/Algorithms/maximum_subarray/rocq/) | linear DP; LeetCode 53 |
| Merging stones | [merging_stones](../benchmarks/Algorithms/merging_stones/rocq/) | minimum-cost interval DP; P1775 |
| Bounded knapsack | [multiple_knapsack](../benchmarks/Algorithms/multiple_knapsack/rocq/) | monotone-queue optimization grouped by residue |
| Paint house II | [paint_house_ii](../benchmarks/Algorithms/paint_house_ii/rocq/) | best and second-best cost per column; LeetCode 265 |
| Rod cutting | [rod_cutting](../benchmarks/Algorithms/rod_cutting/rocq/) | optimal cutting revenue |
| Sightseeing bus | [sightseeing_bus](../benchmarks/Algorithms/sightseeing_bus/rocq/) | departure scheduling and waiting cost; P1315 |
| Stock trading | [stock_trading](../benchmarks/Algorithms/stock_trading/rocq/) | cooldown, holding state and monotone-queue optimization; P2569 |
| Turning off streetlights | [streetlight](../benchmarks/Algorithms/streetlight/rocq/) | interval DP over position state; P1220 |
| 0/1 knapsack | [zero_one_knapsack](../benchmarks/Algorithms/zero_one_knapsack/rocq/) | item prefix × capacity state |

### Greedy, binary search and two pointers (7)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Largest concatenated number: sorting | [concatenating_numbers](../benchmarks/Algorithms/concatenating_numbers/rocq/) | concatenation comparator and lexicographically largest arrangement; P1012 |
| Container with most water: linear | [container_with_most_water_linear](../benchmarks/Algorithms/container_with_most_water_linear/rocq/) | two pointers; LeetCode 11 |
| Container with most water: sorting | [container_with_most_water_nlogn](../benchmarks/Algorithms/container_with_most_water_nlogn/rocq/) | joint sorting of heights and indices, endpoint maintenance; LeetCode 11 |
| Huffman optimal merge cost | [huffman_encoding](../benchmarks/Algorithms/huffman_encoding/rocq/) | repeatedly merging the two smallest weights |
| King's game | [kings_game](../benchmarks/Algorithms/kings_game/rocq/) | exchange argument, sorting and minimizing the maximum reward; P1080 |
| Non-overlapping intervals | [non_overlapping_intervals](../benchmarks/Algorithms/non_overlapping_intervals/rocq/) | interval selection and minimal removals; LeetCode 435 |
| Split array largest sum | [split_array_largest_sum](../benchmarks/Algorithms/split_array_largest_sum/rocq/) | binary search on the answer with a greedy feasibility check; LeetCode 410 |

### Sequences, strings and range queries (6)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Choosing inns | [choosing_inns](../benchmarks/Algorithms/choosing_inns/rocq/) | cumulative counting by colour and valid intervals; P1311 |
| Majority element | [majority_element](../benchmarks/Algorithms/majority_element/rocq/) | candidate cancellation and voting; LeetCode 169 |
| Manacher longest palindromic substring | [manacher](../benchmarks/Algorithms/manacher/rocq/) | palindromic radius array; LeetCode 5 |
| Minimal representation | [minimal_representation](../benchmarks/Algorithms/minimal_representation/rocq/) | lexicographically smallest rotation of a cyclic sequence; P1368 |
| Range maximum query | [rmq](../benchmarks/Algorithms/rmq/rocq/) | sparse-table preprocessing; P3865 |
| Sliding window maximum | [sliding_window_maximum](../benchmarks/Algorithms/sliding_window_maximum/rocq/) | monotone queue; LeetCode 239 |

### Computational geometry (2)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Convex hull with floating-point coordinates | [convex_hull_float](../benchmarks/Algorithms/convex_hull_float/rocq/) | cross-product orientation, stack construction and floating-point comparison |
| Polar-angle sort of planar points | [sort_point](../benchmarks/Algorithms/sort_point/rocq/) | half-planes, cross products, distances and permutation of a point array |

### Graph algorithms (14)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| DFS on an adjacency list | [DFS_adjacency_list](../benchmarks/Algorithms/DFS_adjacency_list/rocq/) | list traversal, monadic implementation and the two-layered relational method |
| DFS on a flat adjacency matrix | [DFS_adjacency_matrix](../benchmarks/Algorithms/DFS_adjacency_matrix/rocq/) | traversal over a one-dimensional matrix encoding |
| DFS on a 2-D adjacency matrix | [DFS_adjacency_matrix_2Darray](../benchmarks/Algorithms/DFS_adjacency_matrix_2Darray/rocq/) | traversal over a two-dimensional array encoding |
| Dijkstra with a decrease-key queue | [Dijkstra_linked_forward_star_decrease_key](../benchmarks/Algorithms/Dijkstra_linked_forward_star_decrease_key/rocq/) | linked forward-star graph and key lowering on relaxation; reuses `priority_queue_decrease_key` |
| Dijkstra with an indexed queue | [Dijkstra_linked_forward_star_index_queue](../benchmarks/Algorithms/Dijkstra_linked_forward_star_index_queue/rocq/) | linked forward-star graph and an index-addressed heap; reuses `priority_queue_index` |
| Floyd–Warshall on a flat matrix | [Floyd_adjacency_matrix](../benchmarks/Algorithms/Floyd_adjacency_matrix/rocq/) | all-pairs shortest paths over a one-dimensional encoding |
| Floyd–Warshall on a 2-D matrix | [Floyd_adjacency_matrix_2Darray](../benchmarks/Algorithms/Floyd_adjacency_matrix_2Darray/rocq/) | triple loop and induction on the intermediate vertex |
| Floyd–Warshall on a row-pointer matrix | [Floyd_adjacency_matrix_ptr](../benchmarks/Algorithms/Floyd_adjacency_matrix_ptr/rocq/) | all-pairs shortest paths with rows addressed by pointers |
| Kosaraju strongly connected components | [kosaraju](../benchmarks/Algorithms/kosaraju/rocq/) | two DFS passes over the graph and its reverse, with the component partition as the refinement target |
| Kruskal minimum spanning tree | [kruskal_union_find](../benchmarks/Algorithms/kruskal_union_find/rocq/) | edge sorting and union-find merging; reuses a `union_find` structure kept outside this repository |
| Prim on an adjacency matrix | [prim_adjacency_matrix](../benchmarks/Algorithms/prim_adjacency_matrix/rocq/) | nearest-vertex maintenance and spanning-tree cost |
| Prim returning the tree matrix | [prim_adjacency_matrix_return_matrix](../benchmarks/Algorithms/prim_adjacency_matrix_return_matrix/rocq/) | builds and returns the spanning tree as a matrix |
| Prim on a forward star | [prim_forward_star](../benchmarks/Algorithms/prim_forward_star/rocq/) | forward-star graph and vertex-by-vertex growth |
| Heap-based Prim on a forward star | [prim_forward_star_heap](../benchmarks/Algorithms/prim_forward_star_heap/rocq/) | priority queue over candidate edges; reuses `priority_queue_decrease_key` |

## Codeforces problems (128)

The problems sit in `examples_shard00` (53) and `examples_shard01` (75). Bands and primary categories come from the dataset metadata and from the sampling records in
[`selection/SELECTION.md`](selection/SELECTION.md).

### Difficulty distribution

| Band | Rating range | Problems |
| --- | --- | --- |
| E | 800–1100 | 43 |
| M1 | 1200–1500 | 42 |
| M2 | 1600–1900 | 29 |
| H1 | 2000–2300 | 9 |
| H2 | 2400–2700 | 4 |
| VH | 2800 and above | 1 |

### Primary category

| Primary category (`primary_class`) | Problems |
| --- | --- |
| core — mainstream algorithmic problems | 86 |
| spec-rich — DP, combinatorics, number theory | 35 |
| constructive — construction problems | 3 |
| other | 2 |
| strings | 1 |
| hard-ds — heavier data structures | 1 |

### Tag frequency

Problem tags are multi-label; the table lists tags occurring at least five times.

| Tag | Count |
| --- | --- |
| greedy | 56 |
| implementation | 53 |
| math | 40 |
| constructive algorithms | 26 |
| dp | 20 |
| brute force | 18 |
| number theory | 16 |
| binary search | 16 |
| sortings | 15 |
| strings | 13 |
| data structures | 12 |
| bitmasks | 10 |
| two pointers | 6 |
| games | 5 |
| graphs | 5 |
| combinatorics | 5 |

### Problem list

| Problem | Rating | Band | Original tags |
| --- | --- | --- | --- |
| [1031/A — Golden Plate](../benchmarks/Codeforces/examples_shard01/P001_1031A_golden_plate/rocq/) | 800 | E | implementation, math |
| [1382/A — Common Subsequence](../benchmarks/Codeforces/examples_shard01/P002_1382A_common_subsequence/rocq/) | 800 | E | brute force |
| [1438/A — Specific Tastes of Andre](../benchmarks/Codeforces/examples_shard01/P003_1438A_specific_tastes_of_andre/rocq/) | 800 | E | constructive algorithms, implementation |
| [1747/A — Two Groups](../benchmarks/Codeforces/examples_shard00/P002_1747A_two_groups/rocq/) | 800 | E | constructive algorithms, greedy |
| [1763/A — Absolute Maximization](../benchmarks/Codeforces/examples_shard00/P003_1763A_absolute_maximization/rocq/) | 800 | E | bitmasks, constructive algorithms, greedy, math |
| [1890/A — Doremy's Paint 3](../benchmarks/Codeforces/examples_shard00/P004_1890A_doremys_paint_3/rocq/) | 800 | E | constructive algorithms |
| [1891/A — Sorting with Twos](../benchmarks/Codeforces/examples_shard00/P005_1891A_sorting_with_twos/rocq/) | 800 | E | constructive algorithms, sortings |
| [2008/B — Square or Not](../benchmarks/Codeforces/examples_shard01/P004_2008B_square_or_not/rocq/) | 800 | E | brute force, math, strings |
| [38/A — Army](../benchmarks/Codeforces/examples_shard00/P006_38A_army/rocq/) | 800 | E | implementation |
| [707/A — Brain's Photos](../benchmarks/Codeforces/examples_shard01/P005_707A_brains_photos/rocq/) | 800 | E | implementation |
| [867/A — Between the Offices](../benchmarks/Codeforces/examples_shard01/P006_867A_between_the_offices/rocq/) | 800 | E | implementation |
| [1313/A — Fast Food Restaurant](../benchmarks/Codeforces/examples_shard01/P007_1313A_fast_food_restaurant/rocq/) | 900 | E | brute force, greedy, implementation |
| [1537/B — Bad Boy](../benchmarks/Codeforces/examples_shard00/P008_1537B_bad_boy/rocq/) | 900 | E | constructive algorithms, greedy, math |
| [1696/B — NIT Destroys the Universe](../benchmarks/Codeforces/examples_shard00/P009_1696B_nit_destroys_the_universe/rocq/) | 900 | E | greedy |
| [26/A — Almost Prime](../benchmarks/Codeforces/examples_shard01/P008_26A_almost_prime/rocq/) | 900 | E | number theory |
| [275/A — Lights Out](../benchmarks/Codeforces/examples_shard01/P009_275A_lights_out/rocq/) | 900 | E | implementation |
| [412/A — Poster](../benchmarks/Codeforces/examples_shard01/P010_412A_poster/rocq/) | 900 | E | greedy, implementation |
| [460/A — Vasya and Socks](../benchmarks/Codeforces/examples_shard01/P011_460A_vasya_and_socks/rocq/) | 900 | E | brute force, implementation, math |
| [48/A — Rock-paper-scissors](../benchmarks/Codeforces/examples_shard00/P010_48A_rock_paper_scissors/rocq/) | 900 | E | implementation, schedules |
| [765/A — Neverending competitions](../benchmarks/Codeforces/examples_shard00/P011_765A_neverending_competitions/rocq/) | 900 | E | implementation, math |
| [1139/B — Chocolates](../benchmarks/Codeforces/examples_shard01/P012_1139B_chocolates/rocq/) | 1000 | E | greedy, implementation |
| [1326/A — Bad Ugly Numbers](../benchmarks/Codeforces/examples_shard00/P012_1326A_bad_ugly_numbers/rocq/) | 1000 | E | constructive algorithms, number theory |
| [1725/B — Basketball Together](../benchmarks/Codeforces/examples_shard01/P013_1725B_basketball_together/rocq/) | 1000 | E | binary search, greedy, sortings |
| [1744/C — Traffic Light](../benchmarks/Codeforces/examples_shard00/P013_1744C_traffic_light/rocq/) | 1000 | E | binary search, implementation, two pointers |
| [1765/E — Exchange](../benchmarks/Codeforces/examples_shard01/P014_1765E_exchange/rocq/) | 1000 | E | brute force, math |
| [1784/A — Monsters (easy version)](../benchmarks/Codeforces/examples_shard00/P014_1784A_monsters_easy_version/rocq/) | 1000 | E | brute force, greedy |
| [2051/C — Preparing for the Exam](../benchmarks/Codeforces/examples_shard01/P015_2051C_preparing_for_the_exam/rocq/) | 1000 | E | constructive algorithms, implementation |
| [371/A — K-Periodic Array](../benchmarks/Codeforces/examples_shard01/P016_371A_k_periodic_array/rocq/) | 1000 | E | greedy, implementation, math |
| [435/A — Queue on Bus Stop](../benchmarks/Codeforces/examples_shard00/P015_435A_queue_on_bus_stop/rocq/) | 1000 | E | implementation |
| [450/A — Jzzhu and Children](../benchmarks/Codeforces/examples_shard00/P016_450A_jzzhu_and_children/rocq/) | 1000 | E | implementation |
| [753/A — Santa Claus and Candies](../benchmarks/Codeforces/examples_shard01/P017_753A_santa_claus_and_candies/rocq/) | 1000 | E | dp, greedy, math |
| [1146/B — Hate "A"](../benchmarks/Codeforces/examples_shard00/P018_1146B_hate_a/rocq/) | 1100 | E | implementation, strings |
| [1382/B — Sequential Nim](../benchmarks/Codeforces/examples_shard01/P018_1382B_sequential_nim/rocq/) | 1100 | E | dp, games |
| [1787/B — Number Factorization](../benchmarks/Codeforces/examples_shard01/P019_1787B_number_factorization/rocq/) | 1100 | E | greedy, math, number theory |
| [1807/G2 — Subsequence Addition (Hard Version)](../benchmarks/Codeforces/examples_shard00/P019_1807G2_subsequence_addition_hard/rocq/) | 1100 | E | bitmasks, dp, greedy, implementation, sortings |
| [1994/B — Fun Game](../benchmarks/Codeforces/examples_shard00/P020_1994B_fun_game/rocq/) | 1100 | E | bitmasks, constructive algorithms, greedy, math |
| [2030/C — A TRUE Battle](../benchmarks/Codeforces/examples_shard00/P021_2030C_a_true_battle/rocq/) | 1100 | E | brute force, games, greedy |
| [245/B — Internet Address](../benchmarks/Codeforces/examples_shard00/P022_245B_internet_address/rocq/) | 1100 | E | implementation, strings |
| [433/A — Kitahara Haruki's Gift](../benchmarks/Codeforces/examples_shard01/P020_433A_kitahara_harukis_gift/rocq/) | 1100 | E | brute force, implementation |
| [602/A — Two Bases](../benchmarks/Codeforces/examples_shard01/P021_602A_two_bases/rocq/) | 1100 | E | brute force, implementation |
| [705/B — Spider Man](../benchmarks/Codeforces/examples_shard01/P022_705B_spider_man/rocq/) | 1100 | E | games, math |
| [765/B — Code obfuscation](../benchmarks/Codeforces/examples_shard00/P023_765B_code_obfuscation/rocq/) | 1100 | E | greedy, implementation, strings |
| [985/A — Chess Placing](../benchmarks/Codeforces/examples_shard01/P023_985A_chess_placing/rocq/) | 1100 | E | implementation |
| [1102/C — Doors Breaking and Repairing](../benchmarks/Codeforces/examples_shard01/P024_1102C_doors_breaking_and_repairing/rocq/) | 1200 | M1 | games |
| [1104/B — Game with string](../benchmarks/Codeforces/examples_shard00/P024_1104B_game_with_string/rocq/) | 1200 | M1 | data structures, implementation, math |
| [1355/A — Sequence with Digits](../benchmarks/Codeforces/examples_shard00/P026_1355A_sequence_with_digits/rocq/) | 1200 | M1 | brute force, implementation, math |
| [1384/A — Common Prefixes](../benchmarks/Codeforces/examples_shard01/P025_1384A_common_prefixes/rocq/) | 1200 | M1 | constructive algorithms, greedy, strings |
| [1800/D — Remove Two Letters](../benchmarks/Codeforces/examples_shard00/P027_1800D_remove_two_letters/rocq/) | 1200 | M1 | data structures, greedy, hashing, strings |
| [2000/D — Right Left Wrong](../benchmarks/Codeforces/examples_shard01/P026_2000D_right_left_wrong/rocq/) | 1200 | M1 | greedy, implementation, two pointers |
| [459/A — Pashmak and Garden](../benchmarks/Codeforces/examples_shard01/P027_459A_pashmak_and_garden/rocq/) | 1200 | M1 | implementation |
| [474/B — Worms](../benchmarks/Codeforces/examples_shard01/P028_474B_worms/rocq/) | 1200 | M1 | binary search, implementation |
| [690/D1 — The Wall (easy)](../benchmarks/Codeforces/examples_shard00/P029_690D1_the_wall_easy/rocq/) | 1200 | M1 |  |
| [817/A — Treasure Hunt](../benchmarks/Codeforces/examples_shard01/P029_817A_treasure_hunt/rocq/) | 1200 | M1 | implementation, math, number theory |
| [1113/B — Sasha and Magnetic Machines](../benchmarks/Codeforces/examples_shard00/P030_1113B_sasha_and_magnetic_machines/rocq/) | 1300 | M1 | greedy, number theory |
| [1194/C — From S To T](../benchmarks/Codeforces/examples_shard00/P031_1194C_from_s_to_t/rocq/) | 1300 | M1 | implementation, strings |
| [1220/C — Substring Game in the Lesson](../benchmarks/Codeforces/examples_shard01/P030_1220C_substring_game_in_the_lesson/rocq/) | 1300 | M1 | games, greedy, strings |
| [1311/C — Perform the Combo](../benchmarks/Codeforces/examples_shard01/P031_1311C_perform_the_combo/rocq/) | 1300 | M1 | brute force |
| [1367/C — Social Distance](../benchmarks/Codeforces/examples_shard00/P032_1367C_social_distance/rocq/) | 1300 | M1 | constructive algorithms, greedy, math |
| [1454/D — Number into Sequence](../benchmarks/Codeforces/examples_shard00/P033_1454D_number_into_sequence/rocq/) | 1300 | M1 | constructive algorithms, math, number theory |
| [1561/C — Deep Down Below](../benchmarks/Codeforces/examples_shard01/P032_1561C_deep_down_below/rocq/) | 1300 | M1 | binary search, greedy, sortings |
| [1737/B — Ela's Fitness and the Luxury Number](../benchmarks/Codeforces/examples_shard01/P033_1737B_elas_fitness_and_the_luxury_number/rocq/) | 1300 | M1 | binary search, implementation, math |
| [1999/E — Triple Operations](../benchmarks/Codeforces/examples_shard01/P034_1999E_triple_operations/rocq/) | 1300 | M1 | dp, implementation, math |
| [288/A — Polo the Penguin and Strings](../benchmarks/Codeforces/examples_shard01/P035_288A_polo_the_penguin_and_strings/rocq/) | 1300 | M1 | greedy |
| [303/A — Lucky Permutation Triple](../benchmarks/Codeforces/examples_shard00/P034_303A_lucky_permutation_triple/rocq/) | 1300 | M1 | constructive algorithms, implementation, math |
| [807/B — T-Shirt Hunt](../benchmarks/Codeforces/examples_shard00/P035_807B_t_shirt_hunt/rocq/) | 1300 | M1 | brute force, implementation |
| [1201/C — Maximum Median](../benchmarks/Codeforces/examples_shard01/P036_1201C_maximum_median/rocq/) | 1400 | M1 | binary search, greedy, math, sortings |
| [1266/C — Diverse Matrix](../benchmarks/Codeforces/examples_shard01/P037_1266C_diverse_matrix/rocq/) | 1400 | M1 | constructive algorithms, greedy, math, number theory |
| [1365/C — Rotation Matching](../benchmarks/Codeforces/examples_shard01/P038_1365C_rotation_matching/rocq/) | 1400 | M1 | constructive algorithms, data structures, greedy, implementation |
| [1705/C — Mark and His Unfinished Essay](../benchmarks/Codeforces/examples_shard00/P036_1705C_mark_and_his_unfinished_essay/rocq/) | 1400 | M1 | brute force, implementation |
| [1875/C — Jellyfish and Green Apple](../benchmarks/Codeforces/examples_shard00/P037_1875C_jellyfish_and_green_apple/rocq/) | 1400 | M1 | bitmasks, greedy, math, number theory |
| [1903/C — Theofanis' Nightmare](../benchmarks/Codeforces/examples_shard00/P038_1903C_theofanis_nightmare/rocq/) | 1400 | M1 | constructive algorithms, greedy |
| [1955/D — Inaccurate Subsequence Search](../benchmarks/Codeforces/examples_shard00/P039_1955D_inaccurate_subsequence_search/rocq/) | 1400 | M1 | data structures, two pointers |
| [1983/C — Have Your Cake and Eat It Too](../benchmarks/Codeforces/examples_shard00/P040_1983C_have_your_cake_and_eat_it_too/rocq/) | 1400 | M1 | binary search, brute force, greedy, implementation |
| [435/B — Pasha Maximizes](../benchmarks/Codeforces/examples_shard01/P039_435B_pasha_maximizes/rocq/) | 1400 | M1 | greedy |
| [81/A — Plug-in](../benchmarks/Codeforces/examples_shard01/P040_81A_plug_in/rocq/) | 1400 | M1 | implementation |
| [1054/C — Candies Distribution](../benchmarks/Codeforces/examples_shard00/P041_1054C_candies_distribution/rocq/) | 1500 | M1 | constructive algorithms, implementation |
| [1538/F — Interesting Function](../benchmarks/Codeforces/examples_shard01/P041_1538F_interesting_function/rocq/) | 1500 | M1 | binary search, dp, math, number theory |
| [1551/C — Interesting Story](../benchmarks/Codeforces/examples_shard00/P042_1551C_interesting_story/rocq/) | 1500 | M1 | greedy, sortings, strings |
| [276/C — Little Girl and Maximum Sum](../benchmarks/Codeforces/examples_shard00/P043_276C_little_girl_and_maximum_sum/rocq/) | 1500 | M1 | data structures, greedy, implementation, sortings |
| [545/C — Woodcutters](../benchmarks/Codeforces/examples_shard00/P044_545C_woodcutters/rocq/) | 1500 | M1 | dp, greedy |
| [555/A — Case of Matryoshkas](../benchmarks/Codeforces/examples_shard01/P042_555A_case_of_matryoshkas/rocq/) | 1500 | M1 | implementation |
| [569/A — Music](../benchmarks/Codeforces/examples_shard00/P045_569A_music/rocq/) | 1500 | M1 | implementation, math |
| [649/C — Печать условий](../benchmarks/Codeforces/examples_shard01/P043_649C_pechat_uslovii/rocq/) | 1500 | M1 | constructive algorithms, greedy, sortings |
| [837/C — Two Seals](../benchmarks/Codeforces/examples_shard01/P044_837C_two_seals/rocq/) | 1500 | M1 | brute force, implementation |
| [959/C — Mahmoud and Ehab and the wrong algorithm](../benchmarks/Codeforces/examples_shard01/P045_959C_mahmoud_and_ehab_and_the_wrong_algorithm/rocq/) | 1500 | M1 | constructive algorithms, trees |
| [1082/C — Multi-Subject Competition](../benchmarks/Codeforces/examples_shard00/P046_1082C_multi_subject_competition/rocq/) | 1600 | M2 | greedy, sortings |
| [1243/B2 — Character Swap (Hard Version)](../benchmarks/Codeforces/examples_shard01/P046_1243B2_character_swap/rocq/) | 1600 | M2 | strings |
| [1523/C — Compression and Expansion](../benchmarks/Codeforces/examples_shard00/P047_1523C_compression_and_expansion/rocq/) | 1600 | M2 | brute force, data structures, greedy, implementation, trees |
| [1582/D — Vupsen, Pupsen and 0](../benchmarks/Codeforces/examples_shard01/P047_1582D_vupsen_pupsen_and_0/rocq/) | 1600 | M2 | constructive algorithms, math |
| [1607/E — Robot on the Board 1](../benchmarks/Codeforces/examples_shard01/P048_1607E_robot_on_the_board_1/rocq/) | 1600 | M2 | implementation |
| [1771/C — Hossam and Trainees](../benchmarks/Codeforces/examples_shard00/P048_1771C_hossam_and_trainees/rocq/) | 1600 | M2 | greedy, math, number theory |
| [1946/C — Tree Cutting](../benchmarks/Codeforces/examples_shard00/P049_1946C_tree_cutting/rocq/) | 1600 | M2 | binary search, dp, greedy, implementation, trees |
| [411/B — Multi-core Processor](../benchmarks/Codeforces/examples_shard01/P049_411B_multi_core_processor/rocq/) | 1600 | M2 | implementation |
| [440/B — Balancer](../benchmarks/Codeforces/examples_shard00/P050_440B_balancer/rocq/) | 1600 | M2 | greedy, implementation |
| [639/B — Bear and Forgotten Tree 3](../benchmarks/Codeforces/examples_shard00/P051_639B_bear_and_forgotten_tree_3/rocq/) | 1600 | M2 | constructive algorithms, graphs, trees |
| [847/H — Load Testing](../benchmarks/Codeforces/examples_shard01/P050_847H_load_testing/rocq/) | 1600 | M2 | greedy |
| [986/A — Fair](../benchmarks/Codeforces/examples_shard01/P051_986A_fair/rocq/) | 1600 | M2 | graphs, greedy, number theory, shortest paths |
| [1168/A — Increasing by Modulo](../benchmarks/Codeforces/examples_shard00/P052_1168A_increasing_by_modulo/rocq/) | 1700 | M2 | binary search, greedy |
| [1393/C — Pinkie Pie Eats Patty-cakes](../benchmarks/Codeforces/examples_shard00/P053_1393C_pinkie_pie_eats_patty_cakes/rocq/) | 1700 | M2 | constructive algorithms, greedy, math, sortings |
| [1594/D — The Number of Imposters](../benchmarks/Codeforces/examples_shard01/P053_1594D_the_number_of_imposters/rocq/) | 1700 | M2 | constructive algorithms, dfs and similar, dp, dsu, graphs |
| [1776/F — Train Splitting](../benchmarks/Codeforces/examples_shard00/P054_1776F_train_splitting/rocq/) | 1700 | M2 | constructive algorithms, graphs, greedy |
| [276/D — Little Girl and Maximum XOR](../benchmarks/Codeforces/examples_shard01/P055_276D_little_girl_and_maximum_xor/rocq/) | 1700 | M2 | bitmasks, dp, greedy, implementation, math |
| [567/C — Geometric Progression](../benchmarks/Codeforces/examples_shard00/P055_567C_geometric_progression/rocq/) | 1700 | M2 | binary search, data structures, dp |
| [630/I — Parking Lot](../benchmarks/Codeforces/examples_shard00/P056_630I_parking_lot/rocq/) | 1700 | M2 | combinatorics, math |
| [65/B — Harry Potter and the History of Magic](../benchmarks/Codeforces/examples_shard01/P056_65B_harry_potter_and_the_history_of_magic/rocq/) | 1700 | M2 | brute force, greedy, implementation |
| [1067/B — Multihedgehog](../benchmarks/Codeforces/examples_shard00/P057_1067B_multihedgehog/rocq/) | 1800 | M2 | dfs and similar, graphs, shortest paths |
| [132/C — Logo Turtle](../benchmarks/Codeforces/examples_shard00/P058_132C_logo_turtle/rocq/) | 1800 | M2 | dp |
| [1355/C — Count Triangles](../benchmarks/Codeforces/examples_shard01/P057_1355C_count_triangles/rocq/) | 1800 | M2 | binary search, implementation, math, two pointers |
| [1721/D — Maximum AND](../benchmarks/Codeforces/examples_shard01/P058_1721D_maximum_and/rocq/) | 1800 | M2 | bitmasks, dfs and similar, divide and conquer, greedy, sortings |
| [1930/D1 — Sum over all Substrings (Easy Version)](../benchmarks/Codeforces/examples_shard01/P060_1930D1_sum_over_all_substrings/rocq/) | 1800 | M2 | brute force, dp, greedy, strings |
| [1492/D — Genius's Gambit](../benchmarks/Codeforces/examples_shard01/P062_1492D_geniuss_gambit/rocq/) | 1900 | M2 | bitmasks, constructive algorithms, greedy, math |
| [1569/D — Inconvenient Pairs](../benchmarks/Codeforces/examples_shard01/P063_1569D_inconvenient_pairs/rocq/) | 1900 | M2 | binary search, data structures, implementation, sortings, two pointers |
| [223/C — Partial Sums](../benchmarks/Codeforces/examples_shard01/P064_223C_partial_sums/rocq/) | 1900 | M2 | combinatorics, math, number theory |
| [535/C — Tavas and Karafs](../benchmarks/Codeforces/examples_shard01/P065_535C_tavas_and_karafs/rocq/) | 1900 | M2 | binary search, greedy, math |
| [1288/D — Minimax Problem](../benchmarks/Codeforces/examples_shard01/P066_1288D_minimax_problem/rocq/) | 2000 | H1 | binary search, bitmasks, dp |
| [21/C — Stripe 2](../benchmarks/Codeforces/examples_shard01/P068_21C_stripe_2/rocq/) | 2000 | H1 | binary search, dp, sortings |
| [509/E — Pretty Song](../benchmarks/Codeforces/examples_shard01/P070_509E_pretty_song/rocq/) | 2000 | H1 | math, strings |
| [1799/D2 — Hot Start Up (hard version)](../benchmarks/Codeforces/examples_shard01/P073_1799D2_hot_start_up/rocq/) | 2100 | H1 | data structures, dp |
| [1474/D — Cleaning](../benchmarks/Codeforces/examples_shard01/P075_1474D_cleaning/rocq/) | 2200 | H1 | data structures, dp, greedy, math |
| [1316/E — Team Building](../benchmarks/Codeforces/examples_shard01/P080_1316E_team_building/rocq/) | 2300 | H1 | bitmasks, dp, greedy, sortings |
| [432/E — Square Tiling](../benchmarks/Codeforces/examples_shard01/P081_432E_square_tiling/rocq/) | 2300 | H1 | constructive algorithms, greedy |
| [623/B — Array GCD](../benchmarks/Codeforces/examples_shard01/P082_623B_array_gcd/rocq/) | 2300 | H1 | dp, greedy, number theory |
| [938/E — Max History](../benchmarks/Codeforces/examples_shard01/P083_938E_max_history/rocq/) | 2300 | H1 | combinatorics, math |
| [498/D — Traffic Jams in the Land](../benchmarks/Codeforces/examples_shard01/P085_498D_traffic_jams_in_the_land/rocq/) | 2400 | H2 | data structures, dp, number theory |
| [639/D — Bear and Contribution](../benchmarks/Codeforces/examples_shard01/P086_639D_bear_and_contribution/rocq/) | 2400 | H2 | data structures, greedy, sortings, two pointers |
| [1027/G — X-mouse in the Campus](../benchmarks/Codeforces/examples_shard01/P090_1027G_x_mouse_in_the_campus/rocq/) | 2600 | H2 | bitmasks, math, number theory |
| [1750/F — Majority](../benchmarks/Codeforces/examples_shard01/P093_1750F_majority/rocq/) | 2700 | H2 | combinatorics, dp, math, strings |
| [1436/F — Sum Over Subsets](../benchmarks/Codeforces/examples_shard01/P096_1436F_sum_over_subsets/rocq/) | 2800 | VH | combinatorics, math, number theory |

## Data structures (5)

| Case | Case directory | Content |
| --- | --- | --- |
| Binary Indexed Tree | [binary_indexed_tree](../benchmarks/Data_structures/binary_indexed_tree/rocq/) | point update, prefix sum and the index ranges covered |
| Array-Based Priority Queue | [priority_queue](../benchmarks/Data_structures/priority_queue/rocq/) | build, sift, pop and heapsort |
| Priority Queue with Decrease-Key | [priority_queue_decrease_key](../benchmarks/Data_structures/priority_queue_decrease_key/rocq/) | position back-mapping, insert, delete and decrease-key |
| Indexed Priority Queue | [priority_queue_index](../benchmarks/Data_structures/priority_queue_index/rocq/) | key–data correspondence and heap operations |
| Array-Based Stack | [stack](../benchmarks/Data_structures/stack/rocq/) | capacity bound, push / pop and bulk construction |

## Engineering (8)

| Case | Case directory | Content |
| --- | --- | --- |
| MiniSat Vector | [minisat/vec](../benchmarks/Engineering/minisat/vec/rocq/) | initialization, access, resizing, appending and destruction of integer and pointer vectors |
| Memory Character Search | [string/memchr](../benchmarks/Engineering/string/memchr/rocq/) | `memchr`: first matching byte within a bounded memory block |
| Memory Operations | [string/memory](../benchmarks/Engineering/string/memory/rocq/) | `memcpy` / `memmove` / `memset`: range copy, overlapping move and fill |
| String and Memory Search | [string/search](../benchmarks/Engineering/string/search/rocq/) | `memchr` / `strchr`: character search in a memory block and in a NUL-terminated string |
| String Concatenation | [string/strcat](../benchmarks/Engineering/string/strcat/rocq/) | `strcat` / `strncat`: concatenation and terminator maintenance, with a bounded variant |
| String Comparison | [string/strcmp](../benchmarks/Engineering/string/strcmp/rocq/) | `strcmp` / `strncmp`: byte-wise comparison and the sign of the lexicographic result |
| String Copy | [string/strcpy](../benchmarks/Engineering/string/strcpy/rocq/) | `strcpy` / `strncpy`: copying, terminator and padding semantics |
| String Length | [string/strlen](../benchmarks/Engineering/string/strlen/rocq/) | `strlen`: length up to the terminator |

## Notes on the data

A case is one independent implementation and may contain several functions. Titles, sources,
Codeforces ratings and the original problem tags are stored in each case's `manifest.json`;
ratings and tags quoted here follow the metadata shipped with the dataset, and `primary_class`
comes from the sampling records under `selection/shards/`.

Input constraints, function interfaces and output requirements are given by the accompanying
`problem.md`, the C function contracts and the Rocq definitions. Some cases use interfaces or
constraints adapted to program verification — for instance function parameters and working
arrays instead of standard input and output.
