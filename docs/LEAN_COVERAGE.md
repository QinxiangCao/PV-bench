# PV-Bench Lean Coverage

The Lean version of PV-Bench provides formal specifications and annotation references for C
program verification, covering classic algorithms, Codeforces problems, data structures and
engineering code. The cases span sorting, number theory, dynamic programming, greedy methods,
graph relations and dynamic memory management.

The Lean version currently contains **83 cases**: 45 algorithms, 34 Codeforces problems,
3 data structures and 1 engineering case. Codeforces ratings range from **800 to 2400**,
from basic algorithmic applications to more involved algorithm design.

Each case's Lean references live in a `lean/` directory next to `rocq/`: `solution_spec.c` with
the function contract, `solution_annotated.c` with the verification annotations, and — where
needed — the specification library `spec_lib.lean` and helper library `helper_lib.lean`. These
files reuse QCP's Lean base libraries; for dependency configuration and build instructions see
the [README](README.md#lean). A `lean/groundtruth/` directory holds the verification
conditions QCP emits for the case, together with a proof script that closes them and has been
checked by Lean. An automated evaluation pipeline is not part of this release.

## Composition

| Category | Cases | Content |
| --- | --- | --- |
| Algorithms (`Algorithms/`) | 45 | sorting, number theory, dynamic programming, greedy methods, sequence processing and computational geometry |
| Competitive problems (`Codeforces/`) | 34 | constructive, math, string, game, graph and optimization problems |
| Data structures (`Data_structures/`) | 3 | binary indexed tree and two priority-queue interfaces |
| Engineering (`Engineering/`) | 1 | MiniSat integer and pointer vectors |
| Total | 83 | |

Cases are counted per independent implementation. Different implementations of the same
algorithm or problem are counted separately — for example five quicksort partition schemes and
two container-with-most-water variants. The full catalogue below links to each case's `lean/`
directory.

## Difficulty distribution and representative cases

### High-rated Codeforces problems

Codeforces ratings are taken from each case's metadata and describe the difficulty of the
original contest problem. Three of the collected problems are rated 2000 or above; the highest
is **639/D — Bear and Contribution (2400)**. The table below summarizes their main features as
seen from the reference implementation and the Lean specification.

| Problem | Rating | Algorithmic and verification features |
| --- | --- | --- |
| [639/D — Bear and Contribution](../benchmarks/Codeforces/examples_shard01/P086_639D_bear_and_contribution/lean/) | 2400 | Scan grouped by target value mod 5, with a heap keeping the k smallest costs. Verification covers the heap representation, accumulated cost and global optimality. |
| [432/E — Square Tiling](../benchmarks/Codeforces/examples_shard01/P081_432E_square_tiling/lean/) | 2300 | Greedy construction of a square tiling. The specification requires every monochromatic component to be a square and the output to be lexicographically smallest, involving 2-D arrays, connectivity and local placement state. |
| [1799/D2 — Hot Start Up (hard version)](../benchmarks/Codeforces/examples_shard01/P073_1799D2_hot_start_up/lean/) | 2100 | Optimized dynamic programming for two-CPU scheduling. Verification covers the normalized state, a global offset and the optimal cost over all valid schedules. |

The difficulty distribution over all 34 Codeforces problems follows. Contest rating and
formal-proof difficulty measure different things: the latter also depends on the mathematical
specification, the loop invariants, the memory representation and the properties to be proved.

| Band | Rating range | Problems |
| --- | --- | --- |
| E | 800–1100 | 20 |
| M1 | 1200–1500 | 10 |
| M2 | 1600–1900 | 1 |
| H1 | 2000–2300 | 2 |
| H2 | 2400 and above | 1 |

### Representative verification problems

Beyond the contest problems, the algorithm, data-structure and engineering cases cover several
kinds of formal-verification problems. The table groups representative cases by the proof task
their specifications and annotations involve.

| Topic | Representative cases | Main verification problem |
| --- | --- | --- |
| Optimized dynamic programming | [multiple_knapsack](../benchmarks/Algorithms/multiple_knapsack/lean/) | Agreement between the monotone-queue state and the optimal-value specification: candidate validity, ordering, window coverage and preservation of the extremum. |
| Number theory | [extended_chinese_remainder_theorem](../benchmarks/Algorithms/extended_chinese_remainder_theorem/lean/), [lucas_theorem](../benchmarks/Algorithms/lucas_theorem/lean/) | Merging congruence systems, gcd and lcm, binomial coefficients and digit decomposition, together with the range conditions of C integer arithmetic. |
| Global optimality | [huffman_encoding](../benchmarks/Algorithms/huffman_encoding/lean/), [kings_game](../benchmarks/Algorithms/kings_game/lean/) | The relation between local choices and global optimality: the minimal cost of a valid Huffman tree, and the optimality of a sorting strategy by an exchange argument. |
| In-place sorting and geometry | five quicksorts starting from [quicksort_hoare_fill_index](../benchmarks/Algorithms/quicksort_hoare_fill_index/lean/), and [sort_point](../benchmarks/Algorithms/sort_point/lean/) | Partition properties, permutation preservation, recursive subranges and splitting of memory resources; polar-angle sorting additionally involves the comparison relation, cross products and the memory representation of points. |
| Data structures | [priority_queue_index](../benchmarks/Data_structures/priority_queue_index/lean/) | Consistency between the heap array and the key–data correspondence, and preservation of heap order and the abstract mapping under build, sift and pop. |
| Engineering | [MiniSat vec](../benchmarks/Engineering/minisat/vec/lean/) | Content preservation across dynamic growth, the memory representation of the initialized region and the remaining capacity, and address computation for integer and pointer vectors. |

## Algorithms (45)

The algorithm cases are divided into six categories by primary method; each case belongs to one.

| Primary category | Cases |
| --- | --- |
| Sorting and discretization | 12 |
| Number theory and modular arithmetic | 10 |
| Dynamic programming | 10 |
| Greedy, binary search and two pointers | 7 |
| Sequences, strings and range queries | 5 |
| Computational geometry | 1 |

### Sorting and discretization (12)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Selection sort | [selection_sort](../benchmarks/Algorithms/selection_sort/lean/) | picks the minimum each round |
| Bidirectional selection sort | [optimized_selection_sort](../benchmarks/Algorithms/optimized_selection_sort/lean/) | picks the minimum and the maximum each round |
| Bubble sort | [bubble_sort](../benchmarks/Algorithms/bubble_sort/lean/) | adjacent swaps and a sorted suffix |
| Insertion sort | [insertion_sort](../benchmarks/Algorithms/insertion_sort/lean/) | sorted prefix and element insertion |
| Stable counting sort | [counting_sort](../benchmarks/Algorithms/counting_sort/lean/) | frequencies, prefix sums and stable placement |
| Decimal radix sort | [bucket_sort](../benchmarks/Algorithms/bucket_sort/lean/) | stable bucketing by decimal digit |
| Quicksort: Hoare fill partition | [quicksort_hoare_fill_index](../benchmarks/Algorithms/quicksort_hoare_fill_index/lean/) | fill-hole partition |
| Quicksort: Hoare fill partition, variant 2 | [quicksort_hoare_fill_index2](../benchmarks/Algorithms/quicksort_hoare_fill_index2/lean/) | another fill-hole implementation |
| Quicksort: Hoare swap partition | [quicksort_hoare_swap_index](../benchmarks/Algorithms/quicksort_hoare_swap_index/lean/) | two-way scan and swap |
| Quicksort: Hoare swap partition, variant 2 | [quicksort_hoare_swap_index2](../benchmarks/Algorithms/quicksort_hoare_swap_index2/lean/) | another swap-partition implementation |
| Quicksort: Lomuto partition | [quicksort_lomuto_index](../benchmarks/Algorithms/quicksort_lomuto_index/lean/) | scanning partition placing the pivot |
| Coordinate discretization | [discretize](../benchmarks/Algorithms/discretize/lean/) | sorting, deduplication and an order-preserving map |

### Number theory and modular arithmetic (10)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Modular multiplication | [modular_mul](../benchmarks/Algorithms/modular_mul/lean/) | doubling-and-adding to avoid overflow of a direct product |
| Fast modular exponentiation | [modular_power](../benchmarks/Algorithms/modular_power/lean/) | binary exponentiation; P1226 |
| Modular inverse | [modular_inverse](../benchmarks/Algorithms/modular_inverse/lean/) | calls the extended Euclidean interface and normalizes the residue |
| Batch modular inverses | [linear_modular_inverse](../benchmarks/Algorithms/linear_modular_inverse/lean/) | linear recurrence for a prime modulus; P3811 |
| Inverse via Euler's theorem | [euler_theorem_inverse](../benchmarks/Algorithms/euler_theorem_inverse/lean/) | coprimality, Euler's totient and modular power |
| Chinese remainder theorem | [chinese_remainder_theorem](../benchmarks/Algorithms/chinese_remainder_theorem/lean/) | congruence system with pairwise coprime moduli; P1495 |
| Extended Chinese remainder theorem | [extended_chinese_remainder_theorem](../benchmarks/Algorithms/extended_chinese_remainder_theorem/lean/) | consistent congruence system with non-coprime moduli; P4777 |
| Lucas' theorem | [lucas_theorem](../benchmarks/Algorithms/lucas_theorem/lean/) | binomial coefficients modulo a prime; P3807 |
| Prime factorization | [integer_divide](../benchmarks/Algorithms/integer_divide/lean/) | prime factors with multiplicity in non-decreasing order |
| Euler's linear sieve | [sieve_of_euler](../benchmarks/Algorithms/sieve_of_euler/lean/) | prime enumeration and composite marking |

### Dynamic programming (10)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Maximum subarray sum | [maximum_subarray](../benchmarks/Algorithms/maximum_subarray/lean/) | linear DP; LeetCode 53 |
| House robber | [house_robber](../benchmarks/Algorithms/house_robber/lean/) | adjacent-exclusive selection; LeetCode 198 |
| Rod cutting | [rod_cutting](../benchmarks/Algorithms/rod_cutting/lean/) | optimal cutting revenue |
| 0/1 knapsack | [zero_one_knapsack](../benchmarks/Algorithms/zero_one_knapsack/lean/) | item prefix × capacity state |
| Bounded knapsack | [multiple_knapsack](../benchmarks/Algorithms/multiple_knapsack/lean/) | monotone-queue optimization grouped by residue |
| Longest common subsequence | [lcs_n](../benchmarks/Algorithms/lcs_n/lean/) | two-dimensional DP |
| Matrix chain multiplication | [matrix_chain_multiplication](../benchmarks/Algorithms/matrix_chain_multiplication/lean/) | interval DP and optimal parenthesization |
| Energy necklace | [energy_necklace](../benchmarks/Algorithms/energy_necklace/lean/) | circular interval DP maximizing merged energy; P1063 |
| Catalan numbers / stack sequences | [catalan_numbers](../benchmarks/Algorithms/catalan_numbers/lean/) | counting valid pop sequences; P1044 |
| Annoying math homework | [annoying_math_homework](../benchmarks/Algorithms/annoying_math_homework/lean/) | digit-sum counting over a range / digit DP; P4999 |

### Greedy, binary search and two pointers (7)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Largest concatenated number: sorting | [concatenating_numbers](../benchmarks/Algorithms/concatenating_numbers/lean/) | concatenation comparator and lexicographically largest arrangement; P1012 |
| Container with most water: linear | [container_with_most_water_linear](../benchmarks/Algorithms/container_with_most_water_linear/lean/) | two pointers; LeetCode 11 |
| Container with most water: sorting | [container_with_most_water_nlogn](../benchmarks/Algorithms/container_with_most_water_nlogn/lean/) | joint sorting of heights and indices, endpoint maintenance; LeetCode 11 |
| Non-overlapping intervals | [non_overlapping_intervals](../benchmarks/Algorithms/non_overlapping_intervals/lean/) | interval selection and minimal removals; LeetCode 435 |
| Huffman optimal merge cost | [huffman_encoding](../benchmarks/Algorithms/huffman_encoding/lean/) | repeatedly merging the two smallest weights |
| King's game | [kings_game](../benchmarks/Algorithms/kings_game/lean/) | exchange argument, sorting and minimizing the maximum reward; P1080 |
| Split array largest sum | [split_array_largest_sum](../benchmarks/Algorithms/split_array_largest_sum/lean/) | binary search on the answer with a greedy feasibility check; LeetCode 410 |

### Sequences, strings and range queries (5)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Choosing inns | [choosing_inns](../benchmarks/Algorithms/choosing_inns/lean/) | cumulative counting by colour and valid intervals; P1311 |
| Majority element | [majority_element](../benchmarks/Algorithms/majority_element/lean/) | candidate cancellation and voting; LeetCode 169 |
| Minimal representation | [minimal_representation](../benchmarks/Algorithms/minimal_representation/lean/) | lexicographically smallest rotation of a cyclic sequence; P1368 |
| Sliding window maximum | [sliding_window_maximum](../benchmarks/Algorithms/sliding_window_maximum/lean/) | monotone queue; LeetCode 239 |
| Range maximum query | [rmq](../benchmarks/Algorithms/rmq/lean/) | sparse-table preprocessing; P3865 |

### Computational geometry (1)

| Problem / implementation | Case directory | Content |
| --- | --- | --- |
| Polar-angle sort of planar points | [sort_point](../benchmarks/Algorithms/sort_point/lean/) | half-planes, cross products, distances and permutation of a point array |

## Codeforces problems (34)

The Codeforces problems are classified by primary solution method; a problem may involve several
methods, and the full tag list is in each case's `manifest.json`. The problems sit in
`examples_shard00` (14) and `examples_shard01` (20).

| Primary category | Problems |
| --- | --- |
| Greedy and constructive | 9 |
| Math, number theory and bitwise | 8 |
| Enumeration, simulation and geometry | 7 |
| Strings and sequence maintenance | 4 |
| Games | 4 |
| DP, binary search and state maintenance | 1 |
| Heaps and cost optimization | 1 |

### examples_shard00 (14)

| Problem | Rating | Primary category |
| --- | --- | --- |
| [1763/A — Absolute Maximization](../benchmarks/Codeforces/examples_shard00/P003_1763A_absolute_maximization/lean/) | 800 | Math, number theory and bitwise |
| [1890/A — Doremy's Paint 3](../benchmarks/Codeforces/examples_shard00/P004_1890A_doremys_paint_3/lean/) | 800 | Greedy and constructive |
| [38/A — Army](../benchmarks/Codeforces/examples_shard00/P006_38A_army/lean/) | 800 | Enumeration, simulation and geometry |
| [1537/B — Bad Boy](../benchmarks/Codeforces/examples_shard00/P008_1537B_bad_boy/lean/) | 900 | Greedy and constructive |
| [1696/B — NIT Destroys the Universe](../benchmarks/Codeforces/examples_shard00/P009_1696B_nit_destroys_the_universe/lean/) | 900 | Greedy and constructive |
| [1326/A — Bad Ugly Numbers](../benchmarks/Codeforces/examples_shard00/P012_1326A_bad_ugly_numbers/lean/) | 1000 | Math, number theory and bitwise |
| [1744/C — Traffic Light](../benchmarks/Codeforces/examples_shard00/P013_1744C_traffic_light/lean/) | 1000 | Strings and sequence maintenance |
| [1784/A — Monsters (easy version)](../benchmarks/Codeforces/examples_shard00/P014_1784A_monsters_easy_version/lean/) | 1000 | Greedy and constructive |
| [2030/C — A TRUE Battle](../benchmarks/Codeforces/examples_shard00/P021_2030C_a_true_battle/lean/) | 1100 | Games |
| [765/B — Code obfuscation](../benchmarks/Codeforces/examples_shard00/P023_765B_code_obfuscation/lean/) | 1100 | Strings and sequence maintenance |
| [1104/B — Game with string](../benchmarks/Codeforces/examples_shard00/P024_1104B_game_with_string/lean/) | 1200 | Strings and sequence maintenance |
| [1355/A — Sequence with Digits](../benchmarks/Codeforces/examples_shard00/P026_1355A_sequence_with_digits/lean/) | 1200 | Math, number theory and bitwise |
| [1113/B — Sasha and Magnetic Machines](../benchmarks/Codeforces/examples_shard00/P030_1113B_sasha_and_magnetic_machines/lean/) | 1300 | Math, number theory and bitwise |
| [807/B — T-Shirt Hunt](../benchmarks/Codeforces/examples_shard00/P035_807B_t_shirt_hunt/lean/) | 1300 | Enumeration, simulation and geometry |

### examples_shard01 (20)

| Problem | Rating | Primary category |
| --- | --- | --- |
| [1438/A — Specific Tastes of Andre](../benchmarks/Codeforces/examples_shard01/P003_1438A_specific_tastes_of_andre/lean/) | 800 | Greedy and constructive |
| [2008/B — Square or Not](../benchmarks/Codeforces/examples_shard01/P004_2008B_square_or_not/lean/) | 800 | Enumeration, simulation and geometry |
| [707/A — Brain's Photos](../benchmarks/Codeforces/examples_shard01/P005_707A_brains_photos/lean/) | 800 | Enumeration, simulation and geometry |
| [460/A — Vasya and Socks](../benchmarks/Codeforces/examples_shard01/P011_460A_vasya_and_socks/lean/) | 900 | Enumeration, simulation and geometry |
| [1139/B — Chocolates](../benchmarks/Codeforces/examples_shard01/P012_1139B_chocolates/lean/) | 1000 | Greedy and constructive |
| [1765/E — Exchange](../benchmarks/Codeforces/examples_shard01/P014_1765E_exchange/lean/) | 1000 | Math, number theory and bitwise |
| [753/A — Santa Claus and Candies](../benchmarks/Codeforces/examples_shard01/P017_753A_santa_claus_and_candies/lean/) | 1000 | Greedy and constructive |
| [1382/B — Sequential Nim](../benchmarks/Codeforces/examples_shard01/P018_1382B_sequential_nim/lean/) | 1100 | Games |
| [602/A — Two Bases](../benchmarks/Codeforces/examples_shard01/P021_602A_two_bases/lean/) | 1100 | Math, number theory and bitwise |
| [705/B — Spider Man](../benchmarks/Codeforces/examples_shard01/P022_705B_spider_man/lean/) | 1100 | Games |
| [459/A — Pashmak and Garden](../benchmarks/Codeforces/examples_shard01/P027_459A_pashmak_and_garden/lean/) | 1200 | Enumeration, simulation and geometry |
| [817/A — Treasure Hunt](../benchmarks/Codeforces/examples_shard01/P029_817A_treasure_hunt/lean/) | 1200 | Math, number theory and bitwise |
| [1220/C — Substring Game in the Lesson](../benchmarks/Codeforces/examples_shard01/P030_1220C_substring_game_in_the_lesson/lean/) | 1300 | Games |
| [435/B — Pasha Maximizes](../benchmarks/Codeforces/examples_shard01/P039_435B_pasha_maximizes/lean/) | 1400 | Greedy and constructive |
| [81/A — Plug-in](../benchmarks/Codeforces/examples_shard01/P040_81A_plug_in/lean/) | 1400 | Strings and sequence maintenance |
| [837/C — Two Seals](../benchmarks/Codeforces/examples_shard01/P044_837C_two_seals/lean/) | 1500 | Enumeration, simulation and geometry |
| [276/D — Little Girl and Maximum XOR](../benchmarks/Codeforces/examples_shard01/P055_276D_little_girl_and_maximum_xor/lean/) | 1700 | Math, number theory and bitwise |
| [1799/D2 — Hot Start Up (hard version)](../benchmarks/Codeforces/examples_shard01/P073_1799D2_hot_start_up/lean/) | 2100 | DP, binary search and state maintenance |
| [432/E — Square Tiling](../benchmarks/Codeforces/examples_shard01/P081_432E_square_tiling/lean/) | 2300 | Greedy and constructive |
| [639/D — Bear and Contribution](../benchmarks/Codeforces/examples_shard01/P086_639D_bear_and_contribution/lean/) | 2400 | Heaps and cost optimization |

## Data structures (3)

| Case | Case directory | Content |
| --- | --- | --- |
| Binary indexed tree | [binary_indexed_tree](../benchmarks/Data_structures/binary_indexed_tree/lean/) | point update, prefix sum and the index ranges covered |
| Array-heap priority queue | [priority_queue](../benchmarks/Data_structures/priority_queue/lean/) | build, sift, pop and heapsort |
| Key–data priority queue | [priority_queue_index](../benchmarks/Data_structures/priority_queue_index/lean/) | key–data correspondence and heap operations |

## Engineering (1)

| Case | Case directory | Content |
| --- | --- | --- |
| MiniSat dynamic vector | [minisat/vec](../benchmarks/Engineering/minisat/vec/lean/) | initialization, access, resizing, appending and destruction of integer and pointer vectors |

## Notes on the data

A case is one independent implementation and may contain several functions. Titles, sources,
Codeforces ratings and the original problem tags are stored in each case's `manifest.json`;
ratings quoted here follow the metadata shipped with the dataset.

Input constraints, function interfaces and output requirements are given by the accompanying
`problem.md`, the C function contracts and the Lean definitions. Some cases use interfaces or
constraints adapted to program verification — for instance function parameters and working
arrays instead of standard input and output.
