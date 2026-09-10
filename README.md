# PV-Bench

A benchmark for measuring how well LLMs do **program verification** — not code generation — on real, human-authored problems.

It has 215 problems. Each one comes with a correct C solution that has been given a formal
spec and checked by [**QCP**](https://www.qua.codes/en/index.html). The proofs are done in one
of two backends, **Rocq** or **Lean 4**. All 215 have a Rocq version; 83 also have a Lean one.

The problems are in four groups, all under `benchmarks/`, next to the build files:

| group | problems | C lines | source |
|---|---:|---:|---|
| `benchmarks/Codeforces/` | 128 | 5,685 | competitive-programming problems, grouped into `examples_shard<NN>/` slices |
| `benchmarks/Algorithms/` | 74 | 4,250 | classic algorithms, one directory per algorithm |
| `benchmarks/Data_structures/` | 5 | 404 | array stack, BIT and three priority-queue interfaces |
| `benchmarks/Engineering/` | 8 | 338 | MiniSat vectors and C string / memory routines |
| total | 215 | 10,677 | |

"C lines" counts the unannotated `solution.c` — the program a model is asked to specify and
verify. They are small by design: a median of 40 lines, 50 on average, from 10 up to 189
(`Algorithms/kosaraju`). The difficulty is in the property to be proved, not in the size of the
code.

[`docs/ROCQ_COVERAGE.md`](docs/ROCQ_COVERAGE.md) and
[`docs/LEAN_COVERAGE.md`](docs/LEAN_COVERAGE.md) break these down by topic, difficulty and tag.


## The tool: QCP

[**QCP**](https://www.qua.codes/en/index.html) verifies annotated C programs using symbolic execution and separation logic. 
It automatically discharges verification conditions where possible and exports the remaining obligations to Rocq or Lean 4. 
This workflow motivates PV-Bench's three tasks: writing specifications, supplying annotations, and completing residual proofs.

Verification combines QCP's automatic reasoning with proof-assistant checking. The released automatic results use `Admitted` / `sorry` without exported proof certificates; they are not independently rechecked by the proof-assistant kernel. See [Verification model](docs/VERIFICATION.md) for details.

## The three tasks

Every problem starts from one fully checked reference version. We cut three tasks out of it.
Each answer is checked by the proof assistant — no test suite, no mutants, nothing is run.

| Stage | Given | Model produces | Oracle |
|---|---|---|---|
| **T1 — Spec** | problem + the whole correct program | the entry-point contract `(Require, Ensure)` | prove the contract means the same as the gold one |
| **T2 — Annotate** | + the gold spec | loop invariants, helper contracts, asserts, ghost bindings | QCP proves all VCs, with the code and spec left byte-for-byte unchanged |
| **T3 — Prove** | + the gold annotations | the manual proofs that are left | the backend closes every manual goal, no `admit`/`Axiom` |


## Layout of each problem

The problem statement, its metadata and the reference C solution do not depend on a backend,
so they stay at the top level. Everything that does depend on one goes in a `rocq/` or
`lean/` subdirectory — including the annotated C, because the annotations are written in that
backend's assertion language.

```
  benchmarks/Codeforces/examples_shard01/P001_1031A_golden_plate/
  benchmarks/Algorithms/bubble_sort/
  ├── problem.md              # NL statement
  ├── manifest.json           # provenance + stratification only
  ├── solution.c              # correct reference C solution, unannotated   (given at T1)
  ├── rocq/
  │   ├── solution_spec.c     # + the entry-point contract                  (T1 target)
  │   ├── spec_lib.v          #   its Rocq defs: Pre, Spec, vocabulary      (T1 target)
  │   ├── solution_annotated.c# + all verification annotations              (T2 target)
  │   ├── [helper_lib.v]      #   annotation-support defs, when needed      (T2 target)
  │   └── groundtruth/        # the VCs QCP emits, plus a checked proof        (T3 target)
  │                           #   that closes them
  └── [lean/]                 # same five entries, Lean 4 instead of Rocq
      ├── solution_spec.c
      ├── spec_lib.lean
      ├── solution_annotated.c
      ├── [helper_lib.lean]
      └── groundtruth/
```

`rocq/` is present for all 215 problems; `lean/` for 83 of them — 45 Algorithms,
34 Codeforces (14 in `examples_shard00`, 20 in `examples_shard01`), 3 Data_structures and
1 Engineering. The `.lean` libraries mirror the corresponding `.v` files; cases without
private definitions import shared libraries directly from the C annotations.

### What `groundtruth/` is for

Running QCP on `solution_annotated.c` emits the verification conditions. `groundtruth/` holds
them, together with one proof script that closes them all. Those proofs were written by an
LLM and then checked by the proof assistant, so what is committed is machine-verified either
way.

| file | written by | role |
|---|---|---|
| `<case>_goal.v` | QCP | the VCs — what T3 has to prove |
| `<case>_proof_auto.v` | QCP | the part QCP discharges by itself |
| `<case>_goal_check.v` | QCP | the oracle: it compiles only if every goal is closed |
| `<case>_proof_manual.v` | by LLM | the proofs QCP could not find — **T3's reference answer** |
| `proof_lib.v` | by LLM | supporting lemmas the manual proof leans on |

So the reference proof is not the criterion; `goal_check` is. A model's T3 answer replaces
`<case>_proof_manual.v` and is judged by whether `goal_check` still compiles — the committed
script only shows that at least one machine-checked proof exists, so the goal is known to be
provable and the case really does verify.

Build products (`.vo`, `.glob`, `.olean`, …) stay out of the repository. To regenerate the
QCP-written files, see [Regenerating groundtruth](#regenerating-groundtruth).

## Setup

All builds run from `benchmarks/`, which holds `Makefile`, `CONFIGURE.example`,
`lakefile.lean` and `lean-toolchain`.

Both backends load QCP's libraries from a checkout whose location differs per machine, so
the resolved configuration (`_CoqProject`, `CONFIGURE`, `lake-manifest.json`) is untracked.
The two backends are independent — set up only the one you need.

### Where the QCP libraries come from

This branch does not ship them; point the build at your own QCP checkout, as described below.

If you would rather not set one up, the **`with-backend`** branch carries a `backend/`
directory with the smallest set of QCP libraries these problems need — 263 `.v` files for Rocq and 11 Lake packages for Lean, copied verbatim from the QCP repository. It is the same
benchmark otherwise, and `benchmarks/CONFIGURE.example` there already points at it:

```sh
git checkout with-backend
cd backend/Rocq && make depend && make -j6   # build the libraries once
cd ../../benchmarks
cp CONFIGURE.example CONFIGURE               # already set to ../backend/Rocq
make -j6
```

See [`backend/README.md`](backend/README.md) on that branch for the Lean equivalent and for
how the directory is kept in sync with upstream.

### Rocq

Use Coq **8.20.1**. Put the path to QCP's `Rocq/` directory in a local `CONFIGURE`;
`make` reads it and passes the library mappings to `coqc` directly:

```sh
cd benchmarks
cp CONFIGURE.example CONFIGURE   # then set QCP_ROCQ to your QCP checkout's Rocq/
make -j6                         # bounded parallelism; never a bare `make -j`
```

`make clean` removes the build products. To check a single file:

```sh
make Algorithms/bubble_sort/rocq/helper_lib.vo
```

`make _CoqProject` writes the mappings out for your editor's Rocq plugin; nothing
in the build reads that file.

### Lean

Use Lean **4.25.2**. Point `qcpLean` at QCP's `Lean/` directory (the one holding
`SeparationLogic/`, `auxlibs/`, `examples/`, …):

```sh
cd benchmarks
QCP_LEAN=/absolute/path/to/QCP/Lean
lake -KqcpLean="$QCP_LEAN" update
lake exe cache get                       # prebuilt Mathlib oleans — see below
lake -KqcpLean="$QCP_LEAN" build
```

**Run `lake exe cache get` before the first build.** QCP's `flocq` and `unifysl` packages
depend on Mathlib, which `update` fetches as source (~650 MB under `.lake/packages/`);
without the cache, Lake compiles Mathlib from scratch, which takes hours instead of seconds.

Lake loads the libraries through `Lean/examples` and compiles the case modules under
`Algorithms/`, `Codeforces/`, `Data_structures/` and `Engineering/`. The QCP library must
provide `AUXLib.Arithmetic`, `AUXLib.Sorting`, `AUXLib.NumberTheory`, `AUXLib.Prime` and
`AUXLib.ZParity`, together with their list, separation-logic and `MaxMinLib` dependencies.
Run `update` again after changing the library path.

To clean, or to check one file:

```sh
lake -KqcpLean="$QCP_LEAN" clean
lake -KqcpLean="$QCP_LEAN" lean path/to/file.lean
```

If a run reports the `qcpLean` option as unset even though you passed `-KqcpLean=`, Lake is
reusing a cached lakefile configuration; remove `.lake/config` and retry.

Either backend builds the specification and helper libraries only; neither runs QCP on the
C programs nor completes their correctness proofs.


## Regenerating groundtruth

`tools/` drives QCP's `symexec` over the annotated C and rewrites `groundtruth/`. It needs
the QCP backend (binaries plus the shared `.strategies`/`.h` that symexec reads), which this
branch does not ship — point `QCP_BACKEND` at one, or use the `with-backend` branch, where
the scripts find `./backend` on their own.

```sh
export QCP_BACKEND=/path/to/backend

tools/gen-rocq.sh                                   # every problem
tools/gen-rocq.sh benchmarks/Algorithms/bubble_sort # one problem
tools/gen-lean.sh benchmarks/Algorithms/bubble_sort # the Lean side

OUT_DIR=/tmp/gt tools/gen-rocq.sh <problem>         # write elsewhere, to diff
```

A `<case>_proof_manual.v` that already holds real proofs (`Qed.`/`Defined.`) is left alone;
pass `--force-manual` to reset it to the generator's template. `proof_lib.v` is not a
generator output and is never touched.

Regenerating is reproducible: for every problem in the benchmark, the goal, proof_auto and
goal_check files come back byte-for-byte identical to the committed ones.

## Contributors

Kan Liu, Qi Liu, Zitong Ni, Lixiang Wang, Shushu Wu, Xiwei Wu, Lihan Xie
