/-
Copyright (c) 2026 Redouane Yagouti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Redouane Yagouti
-/
module

public import AlphaRAR.YDK2026.Deterministic
public import AlphaRAR.ForLMLExplore.MeasureTheory.Function.TendstoInDistribution
public import AlphaRAR.ForLMLExplore.Probability.Distributions.Gaussian.MultivariateGaussianMap
public import AlphaRAR.ForLMLExplore.Probability.Martingale.MartingaleCLT
public import AlphaRAR.ForLMLExplore.SequentialLearning.IsAlgEnvSeq
public import AlphaRAR.ForLMLExplore.SequentialLearning.Means
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Lemma 4.5 of the revised paper: joint CLT with componentwise scaling

Statement written afresh from the revised paper (`arxiv/sections/proof_sketch_emilie.tex`,
`lem:componentwise`), and proved afresh along the paper's proof (Appendix A), independently of
the earlier formalization `estimatorError_joint_tendsto_multivariateGaussian` and of the files it
rests on (`ResponseCLT`, `ResponseCLTJoint`). Only general library results are used: the Lindeberg
martingale CLT (`MartDiffArray.mart_clt`), Cramér–Wold, Slutsky, and the conditional law of a
bandit's feedback.

Paper: under Condition A, for a RAR procedure such that for every `k` there is a deterministic
sequence `c_{n,k} → ∞` with `N_{n,k} / c_{n,k} → 1` a.s., with `D_n = diag(√N_{n,1}, …, √N_{n,K})`,
`D_n (Θ̂_n - Θ) ⇒ 𝒩(0, diag(V_1, …, V_K))`.

Encoding:
* a RAR procedure: any algorithm `alg` run against the bandit `ν` (`IsAlgEnvSeq`);
* Condition A: `E|ξ_{1,k}|² < ∞`, i.e. `MemLp id 2 (ν k)`;
* `c` is deterministic because it does not depend on `ω`;
* `θ_k` is the mean `ν.means k`, `V_k` the variance `Var[id; ν k]`;
* `θ̂_{n,k}` is the paper's estimator (1), `estimator`, with initial values `θ₀`.

Proof, following the paper:
1. For fixed weights `w`, the array `Z_{n,t} = ∑_k w_k X_{t,k}(ξ_{t,k} - θ_k)/√c_{n,k}`
   (`cwIncr`) is a martingale-difference array for the filtration `𝓖_{t-1} = 𝓕_{t-1} ∨ σ(X_t)`
   (`filtrationAction`), with predictable variation `∑_k (w_k²/c_{n,k}) V_k N_{n,k} → ∑_k w_k² V_k`
   and conditional Lindeberg sums tending to `0`; the martingale CLT gives `∑_t Z_{n,t} ⇒
   𝒩(0, ∑_k w_k² V_k)` (`cw_rowSum_tendsto`).
2. Cramér–Wold: `(Q_{n,k}/√c_{n,k})_k ⇒ 𝒩(0, diag V)` (`cw_vector_tendsto`).
3. The Bahadur identity and `N_{n,k}/c_{n,k} → 1`, with Slutsky, give the lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real

open scoped Topology InnerProductSpace

namespace AlphaRAR.Revised

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Fintype 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-! ### One arm is drawn at each step -/

omit [MeasurableSingletonClass 𝓐] in
/-- Exactly one action indicator is `1` at each step: `∑_k X_{t,k} f_k = f_{A_t}`. -/
lemma sum_actionIndicator_mul (A : ℕ → Ω → 𝓐) (t : ℕ) (ω : Ω) (f : 𝓐 → ℝ) :
    ∑ k, actionIndicator A k t ω * f k = f (A t ω) := by
  classical
  rw [Finset.sum_eq_single (A t ω)]
  · simp [actionIndicator]
  · intro k _ hk
    simp [actionIndicator, Ne.symm hk]
  · simp

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] in
lemma actionIndicator_mul_eq_indicator (A : ℕ → Ω → 𝓐) (k : 𝓐) (t : ℕ) (f : Ω → ℝ) :
    (fun ω ↦ actionIndicator A k t ω * f ω) = {ω | A t ω = k}.indicator f := by
  ext ω
  by_cases hk : A t ω = k <;> simp [actionIndicator, hk]

omit [Fintype 𝓐] in
/-- **Conditional expectation given the history and the current action**:
`E[X_{t,k} g_k(ξ_t) | 𝓖_{t-1}] = X_{t,k} ∫ g_k dν_k`, summed over the arms. -/
lemma condExp_sum_actionIndicator_mul [Finite 𝓐] [Fintype 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (t : ℕ)
    (g : 𝓐 → ℝ → ℝ) (hg : ∀ k, StronglyMeasurable (g k))
    (hint : ∀ k, Integrable (fun ω ↦ g k (Y t ω)) P) :
    P[fun ω ↦ ∑ k, actionIndicator A k t ω * g k (Y t ω) | h.filtrationAction t]
      =ᵐ[P] fun ω ↦ ∑ k, actionIndicator A k t ω * (ν k)[g k] := by
  have hset : ∀ k, MeasurableSet {ω | A t ω = k} :=
    fun k ↦ h.measurable_action t (measurableSet_singleton k)
  have hint' : ∀ k, Integrable (fun ω ↦ actionIndicator A k t ω * g k (Y t ω)) P := fun k ↦ by
    rw [actionIndicator_mul_eq_indicator]
    exact (hint k).indicator (hset k)
  have hk : ∀ k, P[fun ω ↦ actionIndicator A k t ω * g k (Y t ω) | h.filtrationAction t]
      =ᵐ[P] fun ω ↦ actionIndicator A k t ω * (ν k)[g k] := fun k ↦ by
    refine (condExp_mul_of_stronglyMeasurable_left
      (h.adapted_actionIndicator_filtrationAction k t).stronglyMeasurable (hint' k)
      (hint k)).trans ?_
    filter_upwards [h.condExp_feedback_comp_stationaryEnv t (hg k) (hint k)] with ω hω
    simp only [Pi.mul_apply, hω]
    by_cases hAk : A t ω = k <;> simp [actionIndicator, hAk]
  have hsum := condExp_finsetSum (s := Finset.univ) (fun k _ ↦ hint' k) (h.filtrationAction t)
  rw [show (fun ω ↦ ∑ k, actionIndicator A k t ω * g k (Y t ω))
      = ∑ k, fun ω ↦ actionIndicator A k t ω * g k (Y t ω) by
    ext ω; simp [Finset.sum_apply]]
  refine hsum.trans ?_
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ hω k

/-! ### Step 1: the weighted martingale-difference array -/

/-- The paper's `Z_{n,t} = ∑_k w_k X_{t,k} (ξ_{t,k} - θ_k) / √c_{n,k}`. -/
noncomputable def cwIncr (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (c : 𝓐 → ℕ → ℝ)
    (w : 𝓐 → ℝ) (n t : ℕ) (ω : Ω) : ℝ :=
  ∑ k, w k / √(c k n) * (actionIndicator A k t ω * (Y t ω - ν.means k))

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
lemma cwIncr_eq_sum (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n t : ℕ) :
    cwIncr ν A Y c w n t
      = fun ω ↦ ∑ k, actionIndicator A k t ω * (w k / √(c k n) * (Y t ω - ν.means k)) := by
  ext ω
  exact Finset.sum_congr rfl fun k _ ↦ by ring

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] in
/-- `Z_{n,t} = w_{A_t} (ξ_t - θ_{A_t}) / √c_{n,A_t}`. -/
lemma cwIncr_apply (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n t : ℕ) (ω : Ω) :
    cwIncr ν A Y c w n t ω
      = w (A t ω) / √(c (A t ω) n) * (Y t ω - ν.means (A t ω)) := by
  rw [cwIncr_eq_sum]
  exact sum_actionIndicator_mul A t ω (fun k ↦ w k / √(c k n) * (Y t ω - ν.means k))

lemma cwIncr_memLp (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n t : ℕ) :
    MemLp (cwIncr ν A Y c w n t) 2 P := by
  have hY := h.memLp_feedback hA t
  refine memLp_finsetSum _ fun k _ ↦ ?_
  have h1 : MemLp (fun ω ↦ actionIndicator A k t ω * (Y t ω - ν.means k)) 2 P := by
    rw [actionIndicator_mul_eq_indicator]
    exact (hY.sub (memLp_const _)).indicator
      (h.measurable_action t (measurableSet_singleton k)).nullMeasurableSet
  exact h1.const_mul _

lemma cwIncr_condExp (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n t : ℕ) :
    P[cwIncr ν A Y c w n t | h.filtrationAction t] =ᵐ[P] 0 := by
  have hY := (h.memLp_feedback hA t).integrable one_le_two
  rw [cwIncr_eq_sum]
  refine (condExp_sum_actionIndicator_mul h t (fun k x ↦ w k / √(c k n) * (x - ν.means k))
    (fun k ↦ (measurable_id.sub_const _).const_mul _ |>.stronglyMeasurable)
    (fun k ↦ (hY.sub (integrable_const _)).const_mul _)).trans ?_
  filter_upwards with ω
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hk : Integrable (fun x : ℝ ↦ x) (ν k) := (hA k).integrable one_le_two
  rw [integral_const_mul, integral_sub hk (integrable_const _), integral_const]
  simp [Kernel.means_apply]

omit [IsProbabilityMeasure P] in
lemma cwIncr_adapted (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n t : ℕ) :
    StronglyMeasurable[h.filtrationAction (t + 1)] (cwIncr ν A Y c w n t) := by
  refine Measurable.stronglyMeasurable ?_
  have hY : Measurable[h.filtrationAction (t + 1)] (Y t) :=
    h.measurable_feedback_filtrationAction_of_lt (Nat.lt_succ_self t)
  have hI : ∀ k, Measurable[h.filtrationAction (t + 1)] (actionIndicator A k t) := fun k ↦
    (h.adapted_actionIndicator_filtrationAction k t).mono (h.filtrationAction.mono t.le_succ)
      le_rfl
  exact Finset.measurable_sum _ fun k _ ↦ ((hI k).mul (hY.sub_const _)).const_mul _

/-- The array `(Z_{n,t})_{t < n}`, with the filtration `𝓖_t = 𝓕_{t-1} ∨ σ(X_t)` in every row. -/
noncomputable def cwArray (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) : MartDiffArray P where
  𝓕 _ := h.filtrationAction
  d := cwIncr ν A Y c w
  k n := n
  memLp := cwIncr_memLp h hA c w
  mgdiff := cwIncr_condExp h hA c w
  adapted := cwIncr_adapted h c w

variable [DecidableEq 𝓐]

omit [Fintype 𝓐] [IsProbabilityMeasure P] in
lemma measurable_pullCount_real (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (k : 𝓐)
    (n : ℕ) : Measurable (fun ω ↦ (pullCount A k n ω : ℝ)) := by
  simp_rw [← count_indicator_eq_pullCount, count]
  exact Finset.measurable_sum _ fun j _ ↦ measurable_actionIndicator k (h.measurable_action j)

omit [DecidableEq 𝓐] in
/-- The conditional variance: `E[Z_{n,t}² | 𝓖_{t-1}] = ∑_k X_{t,k} V_k w_k²/c_{n,k}`. -/
lemma cw_condVar (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n t : ℕ) :
    (cwArray h hA c w).condVar n t =ᵐ[P]
      fun ω ↦ ∑ k, actionIndicator A k t ω * ((w k / √(c k n)) ^ 2 * Var[id; ν k]) := by
  have hsq : (fun ω ↦ (cwIncr ν A Y c w n t ω) ^ 2)
      = fun ω ↦ ∑ k, actionIndicator A k t ω * (w k / √(c k n) * (Y t ω - ν.means k)) ^ 2 := by
    funext ω
    rw [cwIncr_apply, sum_actionIndicator_mul A t ω
      (fun k ↦ (w k / √(c k n) * (Y t ω - ν.means k)) ^ 2)]
  have hY := h.memLp_feedback hA t
  change P[fun ω ↦ (cwIncr ν A Y c w n t ω) ^ 2 | h.filtrationAction t] =ᵐ[P] _
  rw [hsq]
  refine (condExp_sum_actionIndicator_mul h t
    (fun k x ↦ (w k / √(c k n) * (x - ν.means k)) ^ 2)
    (fun k ↦ (((measurable_id.sub_const _).const_mul _).pow_const 2).stronglyMeasurable)
    (fun k ↦ ((hY.sub (memLp_const _)).const_mul _).integrable_sq)).trans ?_
  filter_upwards with ω
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  rw [variance_eq_integral measurable_id.aemeasurable, ← integral_const_mul]
  congr 1
  funext x
  simp only [id, Kernel.means_apply]
  ring

lemma cw_predVar_eq (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (w : 𝓐 → ℝ) (n : ℕ) :
    (cwArray h hA c w).predVar n =ᵐ[P]
      fun ω ↦ ∑ k, (w k / √(c k n)) ^ 2 * Var[id; ν k] * (pullCount A k n ω : ℝ) := by
  filter_upwards [ae_all_iff.mpr fun t ↦ cw_condVar h hA c w n t] with ω hω
  change ∑ t ∈ Finset.range n, (cwArray h hA c w).condVar n t ω = _
  rw [Finset.sum_congr rfl fun t _ ↦ hω t, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← count_indicator_eq_pullCount, count, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ ↦ by ring

/-- The predictable variation tends to `∑_k w_k² V_k`. -/
lemma cw_predVar_tendsto (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1))
    (w : 𝓐 → ℝ) :
    TendstoInMeasure P (fun n ↦ (cwArray h hA c w).predVar n) atTop
      (fun _ ↦ ∑ k, w k ^ 2 * Var[id; ν k]) := by
  have hF : TendstoInMeasure P
      (fun n ω ↦ ∑ k, (w k / √(c k n)) ^ 2 * Var[id; ν k] * (pullCount A k n ω : ℝ)) atTop
      (fun _ ↦ ∑ k, w k ^ 2 * Var[id; ν k]) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (Finset.measurable_sum _ fun k _ ↦
      (measurable_pullCount_real h k n).const_mul _).aestronglyMeasurable) ?_
    filter_upwards [ae_all_iff.mpr hNc] with ω hω
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    have hk := (hω k).const_mul (w k ^ 2 * Var[id; ν k])
    rw [mul_one] at hk
    refine hk.congr' ?_
    filter_upwards [(hc k).eventually_gt_atTop 0] with n hn
    rw [div_pow, sq_sqrt hn.le]
    field_simp
  exact hF.congr' (Eventually.of_forall fun n ↦ (cw_predVar_eq h hA c w n).symm) EventuallyEq.rfl

/-- The conditional Lindeberg sums tend to `0`. -/
lemma cw_lindeberg_tendsto (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1))
    (w : 𝓐 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    TendstoInMeasure P ((cwArray h hA c w).lindeberg · ε) atTop 0 := by
  -- `φ_{n,k}(x) = (a(x - θ_k))² 𝟙{ε < |a(x - θ_k)|}`, with `a = w_k/√c_{n,k}`.
  set φ : ℕ → 𝓐 → ℝ → ℝ := fun n k ↦ {x | ε < |w k / √(c k n) * (x - ν.means k)|}.indicator
    fun x ↦ (w k / √(c k n) * (x - ν.means k)) ^ 2 with hφ
  have hφmeas : ∀ n k, Measurable (φ n k) := fun n k ↦
    (((measurable_id.sub_const _).const_mul _).pow_const 2).indicator
      (measurableSet_lt measurable_const ((measurable_id.sub_const _).const_mul _).abs)
  have hφle : ∀ n k x, ‖φ n k x‖ ≤ (w k / √(c k n) * (x - ν.means k)) ^ 2 := fun n k x ↦ by
    simp only [hφ, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    · simpa using sq_nonneg _
  -- The Lindeberg sums, explicitly.
  have heq : ∀ n, (cwArray h hA c w).lindeberg n ε =ᵐ[P]
      fun ω ↦ ∑ k, (pullCount A k n ω : ℝ) * (ν k)[φ n k] := fun n ↦ by
    have ht : ∀ t, P[{ω | ε < |cwIncr ν A Y c w n t ω|}.indicator
        (fun ω ↦ (cwIncr ν A Y c w n t ω) ^ 2) | h.filtrationAction t]
        =ᵐ[P] fun ω ↦ ∑ k, actionIndicator A k t ω * (ν k)[φ n k] := fun t ↦ by
      have hY := h.memLp_feedback hA t
      have hpt : {ω | ε < |cwIncr ν A Y c w n t ω|}.indicator
          (fun ω ↦ (cwIncr ν A Y c w n t ω) ^ 2)
          = fun ω ↦ ∑ k, actionIndicator A k t ω * φ n k (Y t ω) := by
        funext ω
        rw [sum_actionIndicator_mul A t ω (fun k ↦ φ n k (Y t ω))]
        simp only [hφ, Set.indicator_apply, Set.mem_ofPred_eq, cwIncr_apply]
      rw [hpt]
      refine condExp_sum_actionIndicator_mul h t (φ n) (fun k ↦ (hφmeas n k).stronglyMeasurable)
        fun k ↦ ?_
      refine (((hY.sub (memLp_const _)).const_mul (w k / √(c k n))).integrable_sq).mono'
        ((hφmeas n k).comp (h.measurable_feedback t)).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ hφle n k (Y t ω))
    filter_upwards [ae_all_iff.mpr ht] with ω hω
    change ∑ t ∈ Finset.range n, (P[{ω | ε < |cwIncr ν A Y c w n t ω|}.indicator
        (fun ω ↦ (cwIncr ν A Y c w n t ω) ^ 2) | h.filtrationAction t]) ω = _
    rw [Finset.sum_congr rfl fun t _ ↦ hω t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← count_indicator_eq_pullCount, count, Finset.sum_mul]
  -- `c_{n,k} ∫ φ_{n,k} dν_k → 0`, by dominated convergence.
  have hcI : ∀ k, Tendsto (fun n ↦ c k n * (ν k)[φ n k]) atTop (𝓝 0) := fun k ↦ by
    set ψ : ℕ → ℝ → ℝ := fun n ↦ {x | ε * √(c k n) < |w k * (x - ν.means k)|}.indicator
      fun x ↦ (w k * (x - ν.means k)) ^ 2 with hψ
    have hlim : Tendsto (fun n ↦ ∫ x, ψ n x ∂(ν k)) atTop (𝓝 0) := by
      have hbound : Integrable (fun x ↦ (w k * (x - ν.means k)) ^ 2) (ν k) :=
        (((hA k).sub (memLp_const _)).const_mul (w k)).integrable_sq
      have hdc := tendsto_integral_filter_of_dominated_convergence (μ := ν k) (l := atTop)
        (f := fun _ ↦ 0)
        (F := ψ) _ (Eventually.of_forall fun n ↦
          ((((measurable_id.sub_const _).const_mul _).pow_const 2).indicator
            (measurableSet_lt measurable_const
              ((measurable_id.sub_const _).const_mul _).abs)).aestronglyMeasurable)
        (Eventually.of_forall fun n ↦ ae_of_all _ fun x ↦ by
          simp only [hψ, Set.indicator_apply, Set.mem_ofPred_eq]
          split_ifs
          · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          · simpa using sq_nonneg _) hbound
        (ae_of_all _ fun x ↦ by
          refine tendsto_const_nhds.congr' ?_
          have hs : Tendsto (fun n ↦ ε * √(c k n)) atTop atTop :=
            (tendsto_sqrt_atTop.comp (hc k)).const_mul_atTop hε
          filter_upwards [hs.eventually_ge_atTop |w k * (x - ν.means k)|] with n hn
          simp only [hψ, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right (not_lt.mpr hn)])
      simpa using hdc
    refine hlim.congr' ?_
    filter_upwards [(hc k).eventually_gt_atTop 0] with n hn
    have hs := sqrt_pos.mpr hn
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [hφ, hψ, Set.indicator_apply, Set.mem_ofPred_eq]
    have habs : |w k / √(c k n) * (x - ν.means k)| = |w k * (x - ν.means k)| / √(c k n) := by
      rw [div_mul_eq_mul_div, abs_div, abs_of_pos hs]
    simp only [habs, lt_div_iff₀ hs]
    split_ifs
    · rw [div_mul_eq_mul_div, div_pow, sq_sqrt hn.le]
      field_simp
    · simp
  have hF : TendstoInMeasure P (fun n ω ↦ ∑ k, (pullCount A k n ω : ℝ) * (ν k)[φ n k]) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (Finset.measurable_sum _ fun k _ ↦
      (measurable_pullCount_real h k n).mul_const _).aestronglyMeasurable) ?_
    filter_upwards [ae_all_iff.mpr hNc] with ω hω
    rw [Pi.zero_apply, ← Finset.sum_const_zero (s := (Finset.univ : Finset 𝓐))]
    refine tendsto_finsetSum _ fun k _ ↦ ?_
    have hk := (hω k).mul (hcI k)
    rw [mul_zero] at hk
    refine hk.congr' ?_
    filter_upwards [(hc k).eventually_gt_atTop 0] with n hn
    field_simp
  exact hF.congr' (Eventually.of_forall fun n ↦ (heq n).symm) EventuallyEq.rfl

/-- **Step 1**: `∑_{t<n} Z_{n,t} ⇒ 𝒩(0, ∑_k w_k² V_k)`. -/
lemma cw_rowSum_tendsto (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1))
    (w : 𝓐 → ℝ) :
    TendstoInDistribution (cwArray h hA c w).rowSum atTop id (fun _ ↦ P)
      (gaussianReal 0 (∑ k, w k ^ 2 * Var[id; ν k]).toNNReal) :=
  (cwArray h hA c w).mart_clt
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (sq_nonneg _) (variance_nonneg _ _)) HasLaw.id
    (cw_predVar_tendsto h hA c hc hNc w) fun _ hε ↦ cw_lindeberg_tendsto h hA c hc hNc w hε

/-! ### Step 2: Cramér–Wold -/

/-- The scalar projections of a centred Gaussian with diagonal covariance. -/
lemma multivariateGaussian_diagonal_map_inner (σ : 𝓐 → ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (w : EuclideanSpace ℝ 𝓐) :
    (multivariateGaussian 0 (Matrix.diagonal σ)).map (fun x ↦ ⟪x, w⟫_ℝ)
      = gaussianReal 0 (∑ k, w k ^ 2 * σ k).toNNReal := by
  have hpsd : (Matrix.diagonal σ).PosSemidef := Matrix.PosSemidef.diagonal fun k ↦ hσ k
  have hv : 0 ≤ ∑ k, w k ^ 2 * σ k := Finset.sum_nonneg fun k _ ↦ mul_nonneg (sq_nonneg _) (hσ k)
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ 𝓐) (Matrix.diagonal σ)
  have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ 𝓐 ↦ ⟪x, w⟫_ℝ) μ :=
    (continuous_id.inner continuous_const).measurable.aemeasurable
  refine Measure.ext_of_charFun (funext fun s ↦ ?_)
  calc charFun (μ.map fun x ↦ ⟪x, w⟫_ℝ) s
      = charFun (μ.map fun x ↦ s * ⟪x, w⟫_ℝ) 1 := by
        rw [charFun_map_mul_comp hmeas, mul_one]
    _ = charFun (μ.map fun x ↦ ⟪id x, s • w⟫_ℝ) 1 := by
        simp [real_inner_smul_right]
    _ = charFun μ (s • w) := by
        rw [← charFun_map_eq_charFun_map_inner_one aemeasurable_id, Measure.map_id]
    _ = charFun (gaussianReal 0 (∑ k, w k ^ 2 * σ k).toNNReal) s := by
        rw [charFun_multivariateGaussian hpsd, charFun_gaussianReal, Real.coe_toNNReal _ hv]
        congr 1
        simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, mul_zero, zero_sub,
          Matrix.mulVec_diagonal, dotProduct, PiLp.smul_apply, smul_eq_mul]
        push_cast
        rw [Finset.sum_mul]
        congr 1
        refine congrArg (· / 2) (Finset.sum_congr rfl fun k _ ↦ ?_)
        ring

omit [Fintype 𝓐] in
/-- The normalized response martingales, `(Q_{n,k}/√c_{n,k})_k`. -/
noncomputable def cwVector (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (c : 𝓐 → ℕ → ℝ)
    (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 fun k ↦
    respMG (fun t ↦ actionIndicator A k t ω) (Y · ω) (ν.means k) n / √(c k n)

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [IsMarkovKernel ν] in
/-- `⟨(Q_{n,k}/√c_{n,k})_k, w⟩ = ∑_{t<n} Z_{n,t}`. -/
lemma inner_cwVector (c : 𝓐 → ℕ → ℝ) (w : EuclideanSpace ℝ 𝓐) (n : ℕ) (ω : Ω) :
    ⟪cwVector ν A Y c n ω, w⟫_ℝ = ∑ t ∈ Finset.range n, cwIncr ν A Y c (fun k ↦ w k) n t ω := by
  simp only [cwVector, cwIncr, respMG, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

omit [Fintype 𝓐] [DecidableEq 𝓐] [IsProbabilityMeasure P] in
lemma measurable_cwVector (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (c : 𝓐 → ℕ → ℝ) (n : ℕ) : Measurable (cwVector ν A Y c n) := by
  refine (WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp (Measurable.of_eval fun k ↦ ?_)
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _ fun t _ ↦
    (measurable_actionIndicator k (h.measurable_action t)).mul
      ((h.measurable_feedback t).sub_const _)

/-- **Step 2**: `(Q_{n,k}/√c_{n,k})_k ⇒ 𝒩(0, diag V)`. -/
lemma cw_vector_tendsto (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (c : 𝓐 → ℕ → ℝ) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    TendstoInDistribution (cwVector ν A Y c) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (Matrix.diagonal fun k ↦ Var[id; ν k])) := by
  refine TendstoInDistribution.of_inner aemeasurable_id
    (fun n ↦ (measurable_cwVector h c n).aemeasurable) fun w ↦ ?_
  have hlaw : HasLaw (fun x : EuclideanSpace ℝ 𝓐 ↦ ⟪id x, w⟫_ℝ)
      (gaussianReal 0 (∑ k, w k ^ 2 * Var[id; ν k]).toNNReal)
      (multivariateGaussian 0 (Matrix.diagonal fun k ↦ Var[id; ν k])) :=
    ⟨(continuous_id.inner continuous_const).measurable.aemeasurable,
      multivariateGaussian_diagonal_map_inner _ (fun k ↦ variance_nonneg _ _) w⟩
  refine (tendstoInDistribution_id_iff hlaw).mp ?_
  refine (cw_rowSum_tendsto h hA c hc hNc (fun k ↦ w k)).congr'
    (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ (inner_cwVector c w n ω).symm)
    EventuallyEq.rfl fun n ↦ ((continuous_id.inner continuous_const).measurable.comp
      (measurable_cwVector h c n)).aemeasurable

/-! ### Step 3: from `Q/√c` to `√N (θ̂ - θ)` -/

lemma tendsto_sqrt_div_add_one : Tendsto (fun x : ℝ ↦ √x / (x + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ ↦ 1 / √x) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).congr fun x ↦ (one_div _).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with x hx
    positivity
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← sqrt_div_self']
    exact div_le_div_of_nonneg_left (sqrt_nonneg x) hx (by linarith)

omit [Fintype 𝓐] [DecidableEq 𝓐] [IsProbabilityMeasure P] in
lemma measurable_estimator_apply (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (k : 𝓐)
    (θ₀ : ℝ) (n : ℕ) :
    Measurable (fun ω ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) θ₀ n) := by
  simp only [estimator, count]
  refine Measurable.div ?_ ((Finset.measurable_sum _ fun j _ ↦
    measurable_actionIndicator k (h.measurable_action j)).add_const _)
  exact (Finset.measurable_sum _ fun j _ ↦
    (measurable_actionIndicator k (h.measurable_action j)).mul
      (h.measurable_feedback j)).add_const _

/-- **Lemma 4.5** (revised paper), joint CLT with componentwise scaling. -/
theorem componentwise_clt
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ)
    (hA : ∀ k, MemLp id 2 (ν k))
    (c : 𝓐 → ℕ → ℝ) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    TendstoInDistribution
      (fun n ω ↦ (WithLp.toLp 2 (fun k ↦ √(pullCount A k n ω : ℝ)
        * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k))
          : EuclideanSpace ℝ 𝓐))
      atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (Matrix.diagonal fun k ↦ Var[id; ν k])) := by
  -- `√N_k (θ̂_k - θ_k) = r_k (Q_k/√c_k) + s_k`, with `r → 1` and `s → 0` a.s.
  set r : ℕ → Ω → 𝓐 → ℝ := fun n ω k ↦
    √((pullCount A k n ω : ℝ) / c k n) * (c k n / ((pullCount A k n ω : ℝ) + 1)) with hr
  set s : ℕ → Ω → 𝓐 → ℝ := fun n ω k ↦
    (θ₀ k - ν.means k) * (√(pullCount A k n ω : ℝ) / ((pullCount A k n ω : ℝ) + 1)) with hs
  set g : EuclideanSpace ℝ 𝓐 × ((𝓐 → ℝ) × (𝓐 → ℝ)) → EuclideanSpace ℝ 𝓐 :=
    fun p ↦ WithLp.toLp 2 fun k ↦ p.2.1 k * p.1 k + p.2.2 k with hg_def
  have hg : Continuous g := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k ↦ ?_)
    exact ((continuous_apply k).comp continuous_snd.fst).mul
      ((continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst))
      |>.add ((continuous_apply k).comp continuous_snd.snd)
  have hNmeas := measurable_pullCount_real h
  have hrs_meas : ∀ n, Measurable fun ω ↦ (r n ω, s n ω) := fun n ↦
    (Measurable.of_eval fun k ↦ (((hNmeas k n).div_const _).sqrt.mul
        (measurable_const.div ((hNmeas k n).add_const _)))).prodMk
      (Measurable.of_eval fun k ↦ (((hNmeas k n).sqrt.div
        ((hNmeas k n).add_const _)).const_mul _))
  have hrs : TendstoInMeasure P (fun n ω ↦ (r n ω, s n ω)) atTop
      (fun _ ↦ ((fun _ ↦ (1 : ℝ)), (fun _ ↦ (0 : ℝ)))) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (hrs_meas n).aestronglyMeasurable) ?_
    filter_upwards [ae_all_iff.mpr hNc] with ω hω
    -- `N_k → ∞`, since `N_k/c_k → 1` and `c_k → ∞`.
    have hNtop : ∀ k, Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop := fun k ↦ by
      refine ((hω k).pos_mul_atTop one_pos (hc k)).congr' ?_
      filter_upwards [(hc k).eventually_gt_atTop 0] with n hn
      field_simp
    refine Tendsto.prodMk_nhds (tendsto_pi_nhds.mpr fun k ↦ ?_)
      (tendsto_pi_nhds.mpr fun k ↦ ?_)
    · have h1 : Tendsto (fun n ↦ c k n / ((pullCount A k n ω : ℝ) + 1)) atTop (𝓝 1) := by
        have := ((hω k).add (hc k).inv_tendsto_atTop).inv₀ (by norm_num)
        rw [add_zero, inv_one] at this
        refine this.congr fun n ↦ ?_
        rw [Pi.inv_apply, ← one_div (c k n), ← add_div, inv_div]
      have h2 := (hω k).sqrt
      rw [sqrt_one] at h2
      have h3 := h2.mul h1
      rw [one_mul] at h3
      exact h3
    · have := (tendsto_sqrt_div_add_one.comp (hNtop k)).const_mul (θ₀ k - ν.means k)
      rw [mul_zero] at this
      exact this
  have hmain := (cw_vector_tendsto h hA c hc hNc).continuous_comp_prodMk_of_tendstoInMeasure_const
    hg hrs fun n ↦ (hrs_meas n).aemeasurable
  refine hmain.congr' ?_ ?_ fun n ↦ ?_
  · -- The identity, once every `c_{n,k}` is positive.
    filter_upwards [eventually_all.mpr fun k ↦ (hc k).eventually_gt_atTop 0] with n hn
    refine ae_of_all _ fun ω ↦ ?_
    simp only [hg_def, hr, hs, cwVector]
    congr 1
    funext k
    have hck := hn k
    have hN : (0 : ℝ) ≤ pullCount A k n ω := Nat.cast_nonneg _
    rw [estimator_sub_eq (X := fun j ↦ actionIndicator A k j ω) (Y · ω) (ν.means k) (θ₀ k) n
        (by rw [count_indicator_eq_pullCount]; positivity),
      count_indicator_eq_pullCount, sqrt_div' _ hck.le]
    have hsc : √(c k n) ≠ 0 := (sqrt_pos.mpr hck).ne'
    field_simp
    rw [sq_sqrt hck.le]
    ring
  · exact ae_of_all _ fun x ↦ by simp [hg_def]
  · refine ((WithLp.measurable_toLp 2 (𝓐 → ℝ)).comp
      (Measurable.of_eval fun k ↦ ?_)).aemeasurable
    exact (hNmeas k n).sqrt.mul ((measurable_estimator_apply h k (θ₀ k) n).sub_const _)

end AlphaRAR.Revised
