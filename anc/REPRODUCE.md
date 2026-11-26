# Reproducing the manuscript

The TeX files are in the parent directory of this ancillary folder. From that parent directory, use three pdfLaTeX passes to resolve the references after pagination stabilizes. The document uses amsmath, microtype, hyperref and TikZ.

~~~sh
pdflatex -halt-on-error screening_orders.tex
pdflatex -halt-on-error screening_orders.tex
pdflatex -halt-on-error screening_orders.tex
~~~

Run the scripts below from this ancillary folder. Paths in the experiment notes are relative to this folder. The following scripts use Python's standard library and exact integer or rational arithmetic. Run each with Python 3.9 or later.

| Script | Finite check |
|---|---|
| check_natural_window.py | Cost identities, rank localization examples, signed perturbations and exchanges in interleaved prime bins |
| check_natural_observation.py | The four-prime example, cancellation after recording the largest hits, and finite laws on an integer interval |
| check_rounded_observation.py | Moment perturbations, hidden witness primes, and the budget-dependent estimators for all retained counts at degrees three and four |
| check_stopped_trace.py | Stopped-trace inversion, fixed-priority indistinguishability, adaptive-information bounds and population reconstruction |
| check_local_priorities.py | Two shifted partitions, exact one-hit inversion, prefix moments and recovery of the optimal banded order |
| check_designed_onehit.py | Truncation of centered first-hit scores and second moments of signed first-hit probabilities under preset priorities |
| check_selective_observation.py | Maximal hit sets, importance weights, and information carried by a two-round adaptive record |
| check_structured_pairs.py | Signed feature profiles, comparison with exhaustive feasible orders, split-row rounding, score-tie cubes and bounded-degree graph lifts |
| check_pair_layout.py | Rank repair, multiscale row estimates, capacity discrepancies, and a five-tile integral dynamic program compared with exhaustive search |
| check_natural_hard.py | Forward and inverse noisy-parity experiments on actual integer cells, and exchangeability across one and two bins |
| check_natural_np.py | The graph-order objective after the common prefix, copy blowups and deterministic decoding |
| check_near_uniform.py | Congruence counts and optional stopping in the equal-rate examples |
| check_learning.py | Finite learning lower bounds, optimization and the cutoff comparison |
| check_parity.py | Parity channel identities, midpoint decoding and extremal scores |
| check_clone_amplification.py | Paired planted examples and graph-based word mixtures |

The structured-pair check compares a local profile optimization with exhaustive search. It returns costs 13 and 48 against optima 13 and 43 on its two finite instances. The second instance exercises rounding of a fractional row. The pair-layout checks also cover finite identities and an integral instance. The full two-hit learner, including spectral estimation and the fractional optimization, has a mathematical analysis but no end-to-end timing. The finite-sample experiment below evaluates the scalar learners and requires NumPy. The archived CSVs were generated with version 2.0.2. Use a separate output directory for a fresh run.

~~~sh
python3 natural_experiment.py --out reproduced
~~~

This regenerates four CSVs for two menus. Training draws simulate the joint distribution of the counters used by the learners. The reported costs are population expectations in units of one divisibility check. The column ending in "mean_fraction" reports excess above the population optimum divided by the corresponding excess for increasing-prime order. Full parameters and oracle details are in [the experimental note](natural_experiment.md).

The raw-integer pair experiment uses Python’s standard library. The script generates actual odd words and checks the exact population losses before drawing independent samples. Its ordinary arm and its conditionally sampled arm have different sampling costs. From the archive root run

~~~sh
python3 raw_pair_experiment.py --out reproduced_pairs.csv
~~~

The result contains both menus (100 and 384 candidate primes) with 13,872 rows, including all methods, sample sizes, signs and runs. The 384-prime menu satisfies the size constraint of the natural model. The table in the manuscript averages `regret_over_ascending` for each method at each conditional sample size on that menu. The 100-prime stress example uses a larger prime scale than allowed by that constraint.

The native single-word primality timings are a separate experiment. The archive contains their C++ code, original measurements, library versions, platform and build instructions in [experiment/README.md](experiment/README.md) and [experiment/comparators/README.md](experiment/comparators/README.md). The cutoff-selection experiment is described in [experiment/comparators/cutoff_calibration.md](experiment/comparators/cutoff_calibration.md).

The four-lane 64-bit screen and its scalar baseline are in [experiment/packet_screen/README.md](experiment/packet_screen/README.md), with per-round results from two compilation and timing sessions on the same input lists. A separate experiment on previously sieved streams is in [experiment/rough_dispatch/README.md](experiment/rough_dispatch/README.md).

The end-to-end learned prefilter experiments compare complete deterministic primality calls on two pairs of controlled sources and a uniform-odd control across the two designs. The disjoint-matching experiment, including all-twelve batch and residual-greedy controls, is described in [experiment/learned_order/README.md](experiment/learned_order/README.md). The randomized first-hit experiment and its separate reproduction commands are in [experiment/learned_order/stopped_trials.md](experiment/learned_order/stopped_trials.md). From that directory, running `python3 summarize.py` and `python3 summarize_stopped.py` rebuilds the archived comparisons.
