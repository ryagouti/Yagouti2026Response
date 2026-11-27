# The revised paper: what changed, and how it is formalized

**Source.** The revised LaTeX in `arxiv/`, which is local and not committed. In it, removed text is
red (`revisionred`) and new text is green (`revisiongreen`); the red text is commented out.
Numbers below are those of the compiled revised paper. Lean code is in `AlphaRAR/YDK2026/Revised/`,
one file per result, in the namespace `AlphaRAR.Revised`.

**Status, 2026-11-27.** All five results below are proved in Lean. `scripts/check-build.sh` passes
with no `sorry` and no warnings, and `#print axioms` gives only `propext`, `Classical.choice` and
`Quot.sound` for each. Theorem 5.3 and Corollary 5.5 assume exactly "`ρ` continuous at `Θ`", as the
paper does. Lemma 5.4 and Corollary 5.5 also assume `ρ` measurable, which the paper leaves
implicit.

## 1. What the revision changes

| Revised paper | Change | Old number | Erratum |
|---|---|---|---|
| Lemma 4.5 (`lem:componentwise`) | adds `N_{n,k}/c_{n,k} → 1` a.s. for deterministic `c_{n,k} → ∞` | 4.5 | E1, fixed |
| Definition 5.1 | `h` non-decreasing, `h → ∞`, `h = o(n)` (was `o(√n)`) | 5.1 | E2, fixed |
| Lemma 5.2 (`lem:fe-two-stage`) | new: the RTS-FE hitting times satisfy Lemma 4.4 | — | |
| Theorem 5.3 (`thm:sparse-rate`) | adds "`ρ` continuous at `Θ`", and the rate of `‖Θ̂_n − Θ‖` | 5.2 | |
| Condition C | new: `ρ_k` C² near `Θ` on sparse arms; `√(n log log n) = o(h)`; `h(n − K⌈h⌉ − 1) ∼ h(n)` | — | E2 |
| Lemma 5.4 (`lem:sparse-allocation`) | new: `N_{n,k}/h(n) → 1` a.s. for sparse arms | — | |
| Corollary 5.5 (`corr:componentwise`) | now under Conditions A and C | 5.3 | E2, fixed |
| Lemma 5.7 (`lem:pearson`) | adds the `c_{n,k}` hypothesis and `0 < θ < 1`; moved to Section 5 | 6.1 | E1, fixed |
| Appendix B | new lemmas: weaker last-hitting-time bound, inactivity of forced exploration, forced-exploration lower bound, decay of the sparse target | | |
| Appendix C | adds the martingale CLT (Hall–Heyde, Corollary 3.1); Lemma C.1 constants are now 4 and 12 | | |

Unchanged: Theorems 4.1 and 4.2 and Theorem 5.1. The asymptotic efficiency result is now a remark
(its corollary is commented out); it was not formalized.

## 2. The five results

### Lemma 4.5: joint CLT with componentwise scaling

- **Lean:** `componentwise_clt` in `Revised/ComponentwiseCLT.lean`.
- **Statement:** as in the paper. The Lean version uses `N/c → 1` for each arm; `c` is
  deterministic because it does not depend on `ω`.
- **Proof:** written from scratch along Appendix A. It does not use the earlier formalization
  (`estimatorError_joint_tendsto_multivariateGaussian`) or the files `ResponseCLT` and
  `ResponseCLTJoint`; the only paper files it imports are `Count` and `Deterministic`.

  | Paper step | Lean |
  |---|---|
  | `Z_{n,t}` is a martingale-difference array for `𝓖_{t−1} = 𝓕_{t−1} ∨ σ(X_t)` | `cwIncr`, `cwArray` |
  | `∑_t E[Z²_{n,t} \| 𝓖_{t−1}] → ∑_k a_k² V_k` | `cw_condVar`, `cw_predVar_tendsto` |
  | conditional Lindeberg sums → 0, by dominated convergence | `cw_lindeberg_tendsto` |
  | martingale CLT | `cw_rowSum_tendsto` (via `MartDiffArray.mart_clt`) |
  | Cramér–Wold | `cw_vector_tendsto` |
  | Bahadur identity and Slutsky | `componentwise_clt` |

- **Differences:** none.

### Theorem 5.1, the Theorem 4.1 part: consistency and rates under forced exploration

- **Lean:** `aRTSFE_LLN` in `Revised/ForcedExplorationLLN.lean`.
- **Statement:** the three conclusions of Theorem 4.1 for αRTS-FE, with the limit of `N_{n,k}/n`
  identified as `v_k`. The earlier `aRTSFE_proportion_tendsto` did not identify it.
- **Proof:** the existing abstract hitting-time lemmas (`consistency_of_hitting`,
  `theta_rate_of_hitting`, `rho_rate_of_hitting`) applied to the forced-exploration predicate.
- **Differences:**
  - The paper's `h ≥ 0` is not needed and was dropped, which makes the Lean result more general.
  - Condition B is encoded as in the existing Theorem 4.1: `ρ` is continuous everywhere and
    differentiable at `Θ`, and positive on the closure of the estimator values.
  - The Theorem 4.2 part of Theorem 5.1 was already formalized (`aRTSFE_clt_joint` and others).

### Theorem 5.3: consistency and rate for possibly sparse targets

- **Lean:** `aRTSFE_sparse_rate` in `Revised/SparseRate.lean`.
- **Statement:** all four conclusions, including the new bound
  `‖Θ̂_n − Θ‖ = O(√(log log n / h(n − K⌈h(n)⌉ − 1)))` a.s. (sup norm on `ℝ^K`).
- **Proof:** the per-arm conclusions come from `aRTSFE_sparse_rate_of_continuousAt`. The new
  bound uses forced exploration's floor `N_{n,k} ≥ h(n − K⌈h(n)⌉ − 1)`
  (`eventually_schedShift_le_pullCount`, the paper's `lem:fe-lower-bound`) and
  `exists_rate_loglog_of_pullCount_ge`. It also proves that `n − K⌈h(n)⌉ − 1 → ∞`.
- **Differences:**
  - `h ≥ 0` is not needed and was dropped.
  - Measurability of `ρ` is not needed either.
  - `n − K⌈h(n)⌉ − 1` is natural-number subtraction, which agrees with the paper for large `n`.

### Lemma 5.4: sparse-arm allocation

- **Lean:** `sparse_allocation` and the structure `ConditionC`, in
  `Revised/SparseAllocation.lean`.
- **Statement:** Condition C is encoded clause by clause. `√(n log log n) = o(h)` is an
  `IsLittleO`, and `h(n − K⌈h⌉ − 1) ∼ h(n)` is an `IsEquivalent`.
- **Proof:** Condition C is translated into the hypotheses of the existing argument, and then
  `pullCount_div_sched_tendsto_one` is applied. To make this reuse possible, the step "sparse arms
  are eventually fed only by forced exploration" was moved out of the proof of
  `aRTSFE_sparse_clt_of_contDiffAt` (Corollary 5.5, `ForcedExplorationSparse.lean`) into its own
  lemma, `aRTSFE_fEfed_of_contDiffAt`. The corollary's statement did not change.
- **Differences:** `ρ` is assumed measurable, which the paper leaves implicit (without it the
  plug-in targets `ρ̂_n` are not random variables). `h ≥ 0` is not needed and was dropped.

### Lemma 5.7: asymptotic calibration of the Pearson test

- **Lean:** `pearsonStat_tendsto_chiSquared` in `Revised/PearsonTest.lean`.
- **Statement:** as in the paper. Under `H₀`, every arm is `Ber(θ)` with `0 < θ < 1`. The statistic
  uses `S_{n,k} = N_{n,k} θ̂_{n,k}` with the regularized estimator (1), as the paper writes it. The
  `c_{n,k}` are positive. The limit is Tau Ceti's `chiSquaredMeasure (K − 1)`.
- **Proof:** follows Appendix B, except at one step.

  | Paper step | Lean |
  |---|---|
  | `𝒳_n = σ²/(θ̃(1−θ̃)) · ‖(I − s_n s_nᵀ) Z_n‖²` | `pearsonStat_eq` (algebra in `pearson_algebra`) |
  | `Z_n ⇒ 𝒩(0, I)` by Lemma 4.5 | `pearsonZ_tendsto` (uses `componentwise_clt`) |
  | `θ̃_n → θ` a.s. | `pooledEstimate_tendsto` |
  | `‖s_n − s̄_n‖ → 0` a.s. | `propSqrt_sub_targetSqrt` |
  | `‖(I − ssᵀ) G‖² ∼ χ²_{K−1}` for unit `s` | `stdGaussian_map_projOff` (Cochran, from Tau Ceti) |
  | Skorokhod representation, then Slutsky | subsequence argument, then Slutsky |

- **Difference in the proof, not in the statement.** The paper uses the Skorokhod representation
  theorem, which Mathlib does not have. The Lean proof uses the subsequence criterion
  (`tendsto_of_subseq_tendsto`) instead. The `s̄_n` are unit vectors, so along any subsequence a
  further subsequence converges to some unit vector `s` (compactness of the sphere). Along it, `s_n
  → s` a.s., and Slutsky gives `𝒳_n ⇒ ‖(I − ssᵀ) G‖²`, which is `χ²_{K−1}` for every unit `s`. Since
  every subsequence has a further subsequence with the same limit, the whole sequence converges.
  Both arguments are correct; this one needs only tools already in the library.

## 3. Statements checked against the paper, and small differences

These apply to the statements above and make the Lean results at least as strong as the paper's,
except where noted.

- `IsARTSFE` asks forced exploration to put zero mass outside `S_m`, rather than the uniform
  `1/|S_m|`. It therefore covers more designs.
- The burn-in `m₀` is `0`. The paper says `m₀` does not affect the proofs.
- `ρ` is defined on all of `ℝ^K` with values in the simplex, so a `ρ` given on `H` must be extended.
- `α ∈ [0, 1)`, as in the paper.

## 4. Observations on the revised text

- Lemma 4.5 writes `c_{n,k} → +∞` "a.s.", but `c` is deterministic, so "a.s." can be dropped. The
  same lemma has "there exist a deterministic sequence" (should be "exists").
- Definition 5.1 writes `argmin_{j∈U_m}` with a non-bold `U`; elsewhere the set is bold `𝐔_m`.
- Lemma C.1: the second constant is now 12. The Lean lemma `mart_maximal_dyadic` has 32. This is
  harmless, since the constant is only used inside `O(·)`.
- `sections/05sparse_alloc_func.tex` is empty and not included by `article_arxiv.tex`.

## 5. Continuity at `Θ` only: how it was obtained

The earlier sparse results assumed `ρ` continuous on all of `ℝ^K`. That hypothesis was used in two
ways only:

1. **To show that `ρ̂_n` converges**, in the general consistency lemma `consistency_of_hitting`. That
   lemma is now a wrapper around `consistency_of_hitting_of_rho`, which takes the convergence of
   `ρ̂_n` as a hypothesis. Under forced exploration every arm is sampled infinitely often, so
   `θ̂_n → Θ`, and continuity at `Θ` gives `ρ̂_n → ρ(Θ)`.
2. **For measurability of `ρ`**: `measurableSet_shiftDown_aRTSFEUnder`,
   `not_pulled_of_not_aRTSFEUnder_of_alpha_zero`, `throttled_count_div_sched_tendsto_zero` and
   `fEfed_of_decay` now assume `ρ` measurable instead of continuous.

New general results, in `ForcedExplorationSparse.lean`:
- `aRTSFE_sparse_rate_of_continuousAt` (Theorem 5.3): `ρ` continuous at `Θ`.
- `aRTSFE_sparse_clt_of_continuousAt` (Corollary 5.5): `ρ` measurable and continuous at `Θ`.
- `aRTSFE_fEfed_of_contDiffAt`: now with `ρ` measurable and continuous at `Θ`.

The old theorems `aRTSFE_sparse_rate_of_isARTSFE` and `aRTSFE_sparse_clt_of_contDiffAt` keep their
statements, as one-line wrappers, so the `comparator/` challenges are unchanged; `lake build
Comparator` succeeds. Theorems 4.1, 4.2 and 5.1 are not affected.

## 6. Open

1. Comparator challenges for the new results in `Revised/`, if wanted.

`formalization.yaml` and the blueprint were updated on 2026-11-27. `formalization.yaml` has the
revised numbering (v1 numbers in parentheses), the new results and their Lean declarations, and E1
and E2 marked as resolved. In the blueprint, `normality.tex` (Lemma 4.5), `forced.tex` (Section 5:
the schedule condition, Lemmas B.2 and B.3, Theorem 5.3 with its new rate, Condition C, Lemma 5.4,
Corollary 5.5) and `hypothesis_testing.tex` (Lemma 5.7 with its subsequence proof) follow the
revised paper, and `thm:cochran` points to Tau Ceti's theorem. `scripts/check-blueprint.py` passes,
and every name in `blueprint/lean_decls` exists in Lean.
