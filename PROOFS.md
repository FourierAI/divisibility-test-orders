# Formal verification by numbered result

The numbers and pages refer to the original 74-page manuscript. A partial entry identifies a proved step and the remaining mathematical work. Open entries have no corresponding formal proof of the stated result in this repository. Proposition 39 is indexed under its corrected positive-input statement, with the original signed-domain counterexample linked.

<a id="claim-01"></a>

### Theorem 1 · Information in the count and largest hits

Page 4. Status **partial**.

The finite proxy bound uses operational scan costs. The signed family is realized on odd integers under explicit finite interval conditions. For interleaved bins the inversion lower bound follows from a single-swap margin, and the exact expected inversion count under fair signs is verified. The two-law conclusion requires indistinguishable records and a cost gap.

- [`Screening.CostMoments.operational_counted_surrogate_regret`](lean/Screening/CostMoments.lean#L605)
- [`Screening.Indistinguishability.paired_laws_lower`](lean/Screening/Indistinguishability.lean#L222)
- [`Screening.PrimeIntervalWitness.paper_signed_family`](lean/Screening/PrimeIntervalWitness.lean#L400)
- [`Screening.HardBinRegret.anchor_tail_survival`](lean/Screening/HardBinRegret.lean#L90)
- [`Screening.HardBinRegret.inversion_regret`](lean/Screening/HardBinRegret.lean#L250)
- [`Screening.HardBinRegret.fair_inversion_mean`](lean/Screening/HardBinRegret.lean#L377)

Remaining work — Derive the asymptotic prime-bin estimates, the conditional ties and signed cost gap, and the full precision-dependent sample guarantee.

<a id="claim-02"></a>

### Theorem 2 · Stopped traces

Page 4. Status **partial**.

The probability of a saturated stopped record is derived by inclusion-exclusion; its integer-weight expansion separates the top-degree sum.

- [`Screening.StoppedTrace.saturated_trace_inversion`](lean/Screening/StoppedTrace.lean#L200)
- [`Screening.StoppedTrace.top_degree_trace_sum`](lean/Screening/StoppedTrace.lean#L146)

Remaining work — Prove the truncation multiplicity, adaptive information lower bound, and sample rate with all parameters.

<a id="claim-03"></a>

### Theorem 3 · Preset first-hit priorities at all sample sizes

Page 5. Status **partial**.

The two whole-menu scans and their public randomness define a shared first-hit record. Projecting this record to a chosen pivot gives the local decoder, its exact mean and its second-moment bound.

- [`Screening.OneHitInversion.population_prefix_unbiased`](lean/Screening/OneHitInversion.lean#L369)
- [`Screening.OneHitInversion.observed_second_moment`](lean/Screening/OneHitInversion.lean#L540)
- [`Screening.GlobalOneHit.record_projection`](lean/Screening/GlobalOneHit.lean#L314)
- [`Screening.GlobalOneHit.actual_pivot_mean`](lean/Screening/GlobalOneHit.lean#L406)
- [`Screening.GlobalOneHit.actual_pivot_energy`](lean/Screening/GlobalOneHit.lean#L443)
- [`Screening.GlobalOneHit.simultaneous_raw_prefixes`](lean/Screening/GlobalOneHit.lean#L682)
- [`Screening.PartitionWindows.pivot_forward_cover`](lean/Screening/PartitionWindows.lean#L279)
- [`Screening.MedianLearner.median_scan_regret`](lean/Screening/MedianLearner.lean#L130)
- [`Screening.GlobalOneHit.literal_prefix_mean`](lean/Screening/GlobalOneHit.lean#L918)
- [`Screening.GlobalOneHit.literal_prefix_confidence`](lean/Screening/GlobalOneHit.lean#L939)

Remaining work — Prove the upper and lower minimax envelopes across every sample budget and precision regime.

<a id="claim-04"></a>

### Theorem 4 · Selective supplemental messages

Page 6. Status **partial**.

Lemma 13 bounds the information in one use of a randomized encoder, including the contribution from silence, for arbitrary measurable marked contents.

- [`ScreeningAnalysis.MessageKL.encoder_information`](analysis_lean/ScreeningAnalysis/MessageKL.lean#L114)
- [`ScreeningAnalysis.GeneralMessageKL.product_encoder_information`](analysis_lean/ScreeningAnalysis/GeneralMessageKL.lean#L324)

Remaining work — Derive the multi-round KL lower bound, hard-family decoding, and the matching message and word upper bounds.

<a id="claim-05"></a>

### Proposition 5 · Public stages for set cover

Page 8. Status **open**.

Remaining work — Verify both minimax statements and their reductions to the staged experiment.

<a id="claim-06"></a>

### Proposition 6 · Sparse second-hit supplements

Page 8. Status **open**.

Remaining work — Derive the expected disclosure count, polynomial optimizer and regret at the stated precision.

<a id="claim-07"></a>

### Theorem 7 · Natural arithmetic window and learning threshold

Page 9. Status **partial**.

Finite nonadjacent exchange, the reciprocal-gap window, a signed family on actual integers, and rank displacement are checked.

- [`Screening.NaturalWindow.truncated_arithmetic_optimum_window`](lean/Screening/NaturalWindow.lean#L962)
- [`Screening.PrimeIntervalWitness.paper_signed_family`](lean/Screening/PrimeIntervalWitness.lean#L400)

Remaining work — Instantiate the analytic prime-count bounds and prove the matching statistical minimax rates and running time.

<a id="claim-08"></a>

### Proposition 8 · Scalar scores at finer accuracy

Page 12. Status **open**.

Remaining work — Prove the scalar score approximation, training guarantee, and bit complexity.

<a id="claim-09"></a>

### Theorem 9 · Natural model at all accuracies

Page 14. Status **partial**.

The centered full-order cost is recovered from literal scans and maximal ranks, and the arithmetic window is proved given finite envelopes and interval occupancy.

- [`Screening.CostMoments.centered_cost_eq_trueScore_extended`](lean/Screening/CostMoments.lean#L582)
- [`Screening.NaturalWindow.truncated_arithmetic_optimum_window`](lean/Screening/NaturalWindow.lean#L962)

Remaining work — Prove the uniform concentration bound, tie construction, confidence lower bounds, and the dynamic program.

<a id="claim-10"></a>

### Proposition 10 · Number of priorities for reconstruction

Page 19. Status **partial**.

The Boolean subset inversion that recovers a required containment weight from exclusion queries is checked.

- [`Screening.StoppedTrace.recover_required`](lean/Screening/StoppedTrace.lean#L71)

Remaining work — Prove the block incidence ranks, entire preset query design, and adaptive rank lower bound.

<a id="claim-11"></a>

### Proposition 11 · Local randomized first-hit learner

Page 20. Status **partial**.

The two whole-menu scans and their public randomness define a shared first-hit record. Projecting this record to a chosen pivot gives the local decoder, its exact mean and its second-moment bound. The literal clipped partitions cover the required forward windows. Independent blocks of the same raw records yield a simultaneous finite failure bound. Separately, taking prefix medians and minimizing their sum gives a finite scan-regret bound under uniform block-majority conditions. The decoded expectation coincides with the actual centered survival for every prefix in the displacement band, including empty-hit words.

- [`Screening.OneHitInversion.population_prefix_unbiased`](lean/Screening/OneHitInversion.lean#L369)
- [`Screening.OneHitInversion.local_prefix_concentration`](lean/Screening/OneHitInversion.lean#L866)
- [`Screening.OneHitInversion.two_shift_cover`](lean/Screening/OneHitInversion.lean#L895)
- [`Screening.SampleVariance.block_means_amplified`](lean/Screening/SampleVariance.lean#L409)
- [`Screening.GlobalOneHit.record_projection`](lean/Screening/GlobalOneHit.lean#L314)
- [`Screening.GlobalOneHit.actual_pivot_mean`](lean/Screening/GlobalOneHit.lean#L406)
- [`Screening.GlobalOneHit.actual_pivot_energy`](lean/Screening/GlobalOneHit.lean#L443)
- [`Screening.GlobalOneHit.simultaneous_raw_prefixes`](lean/Screening/GlobalOneHit.lean#L682)
- [`Screening.PartitionWindows.pivot_forward_cover`](lean/Screening/PartitionWindows.lean#L279)
- [`Screening.MedianLearner.median_scan_regret`](lean/Screening/MedianLearner.lean#L130)
- [`Screening.GlobalOneHit.literal_prefix_mean`](lean/Screening/GlobalOneHit.lean#L918)
- [`Screening.GlobalOneHit.literal_prefix_confidence`](lean/Screening/GlobalOneHit.lean#L939)

Remaining work — Connect the centered physical-prefix numerators and their common denominators to the uncentered median scan-cost theorem for all candidate plans. Extend finite rational populations to arbitrary real laws and derive the final rounded sample and confidence rates.

<a id="claim-12"></a>

### Proposition 12 · Lower bound for preset priorities

Page 23. Status **open**.

Remaining work — Prove the lower bounds for all precisions with the stated protocol and confidence.

<a id="claim-13"></a>

### Lemma 13 · Information per supplemental message

Page 26. Status **proved**.

For the free record of this paper (a count and finitely many indices), the 4η² P(send) bound holds for every common retaining randomized encoder. The proof uses actual KL divergence and an arbitrary measurable space for marked contents. It integrates over both silence and marked outputs. The implementation permits any countable free-record alphabet with measurable singletons.

- [`ScreeningAnalysis.MessageKL.encoder_information`](analysis_lean/ScreeningAnalysis/MessageKL.lean#L114)
- [`ScreeningAnalysis.GeneralMessageKL.product_encoder_information`](analysis_lean/ScreeningAnalysis/GeneralMessageKL.lean#L324)

<a id="claim-14"></a>

### Proposition 14 · Rounded lower moments

Page 28. Status **open**.

Remaining work — Establish all degree-dependent upper and lower radii with a single confidence parameter.

<a id="claim-15"></a>

### Theorem 15 · Rounded precision and message budgets

Page 30. Status **open**.

Remaining work — Combine truncated observation layers, separate budgets and the matching hard laws.

<a id="claim-16"></a>

### Lemma 16 · Separated prime bins

Page 33. Status **open**.

Remaining work — Prove the analytic prime estimates and construct the required separated bins in polynomial time.

<a id="claim-17"></a>

### Theorem 17 · Polynomial learner from pairs

Page 33. Status **open**.

Remaining work — Verify accuracy, semidefinite sampling bounds, optimizer, and the full batch running time.

<a id="claim-18"></a>

### Proposition 18 · Deterministic pair optimization

Page 35. Status **open**.

Remaining work — Verify deterministic optimization and its complexity at the stated precision.

<a id="claim-19"></a>

### Lemma 19 · Repair of bucket counts

Page 38. Status **open**.

Remaining work — Formalize both cost bounds, rank repairs and preservation of all promised precedences.

<a id="claim-20"></a>

### Lemma 20 · Sampling rank-dependent potentials

Page 39. Status **open**.

Remaining work — Prove the multiscale uniform error and coding length for all receiving rows.

<a id="claim-21"></a>

### Lemma 21 · Dynamic programming for pair cost

Page 41. Status **open**.

Remaining work — Verify the state representation, cost approximation and complexity bounds.

<a id="claim-22"></a>

### Lemma 22 · Low-rank endpoint

Page 43. Status **open**.

Remaining work — Prove the spectral approximation and state-count estimates for the optimizer.

<a id="claim-23"></a>

### Lemma 23 · Estimating the local spectrum

Page 45. Status **open**.

Remaining work — Prove the simultaneous spectral remainder and sample complexity bounds.

<a id="claim-24"></a>

### Proposition 24 · Lower bound on row-potential lists

Page 46. Status **open**.

Remaining work — Prove the separated coding construction and expected output-size lower bound.

<a id="claim-25"></a>

### Proposition 25 · Arithmetic realization of row potentials

Page 48. Status **open**.

Remaining work — Verify that the packed fields are realized with the specified arithmetic bounds.

<a id="claim-26"></a>

### Proposition 26 · NP-hardness of the natural ordering problem

Page 49. Status **open**.

Remaining work — Formalize the source hardness assumption, polynomial reduction and extraction of a graph order.

<a id="claim-27"></a>

### Theorem 27 · Gap-ETH limit for natural inputs

Page 51. Status **open**.

Remaining work — Prove the promise-gap translation, instance growth and time bounds.

<a id="claim-28"></a>

### Theorem 28 · Matched budgets on a structured class

Page 53. Status **open**.

Remaining work — Assemble the statistical and computational upper/lower bounds on the same class.

<a id="claim-29"></a>

### Theorem 29 · Fine-accuracy noisy-parity reduction

Page 54. Status **open**.

Remaining work — Prove the distribution-preserving reduction, error calibration and resource bounds.

<a id="claim-30"></a>

### Lemma 30 · Embedding equalized marginals

Page 60. Status **partial**.

The signed-cube preservation of lower moments and the uniform lifting of finite rational cell probabilities to individual words are checked.

- [`Screening.MomentCube.superposition_preserves_lower`](lean/Screening/MomentCube.lean#L280)
- [`Screening.CellLift.lift_rational_cell_law`](lean/Screening/CellLift.lean#L169)

Remaining work — Construct the equalized reference and check its quantitative closeness and every hypothesis for this different prime interval.

<a id="claim-31"></a>

### Theorem 31 · Equalized sample complexity

Page 60. Status **open**.

Remaining work — Prove the matching learning curves for the equalized model.

<a id="claim-32"></a>

### Theorem 32 · Parity learning equivalence

Page 62. Status **open**.

Remaining work — Verify both reductions and their exact change in resource parameters.

<a id="claim-33"></a>

### Proposition 33 · Midpoint decoding calibration

Page 64. Status **open**.

Remaining work — Prove the full two-sided calibration and both sharpness examples.

<a id="claim-34"></a>

### Proposition 34 · Low-degree detection bound

Page 65. Status **open**.

Remaining work — Establish the low-degree likelihood bound under the stated limiting condition.

<a id="claim-35"></a>

### Theorem 35 · Even-arity polynomial learner

Page 66. Status **open**.

Remaining work — Prove the flattening estimator, rounding, regret and polynomial complexity.

<a id="claim-36"></a>

### Theorem 36 · Odd-arity polynomial learner

Page 67. Status **open**.

Remaining work — Prove the odd-arity estimator and its stated complexity.

<a id="claim-37"></a>

### Proposition 37 · Log-free odd-arity budget

Page 69. Status **open**.

Remaining work — Verify the cited algorithm interface and reduction yielding the improved budget.

<a id="claim-38"></a>

### Proposition 38 · Hardness with an explicit histogram

Page 70. Status **open**.

Remaining work — Verify the min-sum vertex-cover reduction and the approximation-scheme implication.

<a id="claim-39"></a>

### Proposition 39 · Relative cost of a cutoff

Page 70. Status **partial**.

The linked edition explicitly restricts the support to consecutive positive odd integers. Taken literally on signed integers, with proper factors defined by 1 < p < |w|, the printed condition on the largest input admits a counterexample. For L=2 take the uniform distribution on −3M and −3M+2, with M the product of the m distinct odd menu primes. Each prime has hit probability 1/2. With fallback cost 3, the full scan costs (m+4)/2 and a singleton is optimal at 5/2. Lean constructs menus of arbitrary size. For positive odd inputs a separate finite proof bounds the two-prime hit probability and proves both the optimal independent cutoff and a quantitative transfer to actual scan costs under finite survival brackets.

- [`Screening.SignedCutoffCounterexample.menus_exist`](lean/Screening/SignedCutoffCounterexample.lean#L45)
- [`Screening.SignedCutoffCounterexample.interval_conditions`](lean/Screening/SignedCutoffCounterexample.lean#L77)
- [`Screening.SignedCutoffCounterexample.hits_exactly_first`](lean/Screening/SignedCutoffCounterexample.lean#L89)
- [`Screening.SignedCutoffCounterexample.optimal_costs`](lean/Screening/SignedCutoffCounterexample.lean#L137)
- [`Screening.SignedCutoffCounterexample.no_uniform_factor`](lean/Screening/SignedCutoffCounterexample.lean#L153)
- [`Screening.PositiveCutoff.pair_probability_bound`](lean/Screening/PositiveCutoff.lean#L83)
- [`Screening.PositiveCutoff.independent_cutoff`](lean/Screening/PositiveCutoff.lean#L173)
- [`Screening.PositiveCutoff.relative_cutoff_transfer`](lean/Screening/PositiveCutoff.lean#L254)

Remaining work — Prove the prime-count estimate and combine all finite bounds to derive the stated logarithmic asymptotic ratio on the corrected positive domain.

<a id="claim-40"></a>

### Proposition 40 · Sharpness of the cutoff rate

Page 71. Status **partial**.

For the two stated pair-survival laws with Bq=1, Lean derives each cutoff cost from the prefix sum. For any probability weights on cutoffs it proves the worst expected excess against the two feasible endpoint actions is at least half the separation. Comparing to the respective optima only increases that excess.

- [`ScreeningAnalysis.Cutoff.signed_cost`](analysis_lean/ScreeningAnalysis/Cutoff.lean#L44)
- [`ScreeningAnalysis.Cutoff.randomized_cutoff_gap`](analysis_lean/ScreeningAnalysis/Cutoff.lean#L54)

Remaining work — Instantiate the admissible equalized pair-hit laws on words and the asymptotic positive separation relative to the optimal costs.

<a id="claim-41"></a>

### Theorem 41 · Planted sparse pair family

Page 71. Status **open**.

Remaining work — Verify the information bounds, learner, and planted-clique implication under their stated hypotheses.
