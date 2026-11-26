# Learning Divisibility Test Orders from the Largest Hits

Code and data for the manuscript by Zhipeng Ye, Feng Jiang, and Hao LI. The paper studies which observations of earlier integers suffice to learn a low-cost order for trial division. The mathematical bounds use a specified family of input distributions. The runtime measurements describe the individual workloads and machines in the experiment logs.

## Reproduce the proofs and experiments

| Task | Entry point |
|---|---|
| Build the Lean proofs and audit the axioms used by their proof terms | Run `lake build` inside [lean](lean). The toolchain is Lean 4.19.0. |
| See which steps of the paper are formalized | [Proof guide in Chinese](lean/README.md) |
| Run the arithmetic and combinatorial checks | Run `python3 tools/check_experiments.py` from the repository root. |
| Reproduce the simulations and examine the native benchmarks | [Ancillary reproduction notes](anc/REPRODUCE.md) and [C++ benchmarks](anc/experiment/README.md) |
| Compare trained and fixed prefilters after an input distribution changes | [First-hit experiment](anc/experiment/learned_order/onehit_shift/README.md) and [disjoint-pair control](anc/experiment/learned_order/shift_stress/README.md) |

The 74-page manuscript's ancillary files are preserved under `anc/`. The two distribution-shift studies and the finite-menu certificate checks extend the measurements in that archive. The checksum of the original preprint source archive is `88510f239aa2bc8cac49aefdba555418cefd23b62f5d32aa3eab1d09b72e41e4`.

The source uses Python's standard library for the finite checks. The native performance comparisons have separate compiler, platform, and library requirements documented alongside each experiment. Their recorded nanosecond timings are measurements. The Lean checks concern mathematical correctness.

OpenAI Codex assisted with mathematical constructions, proof development, code, tests, and manuscript preparation.
