/-
Copyright (c) 2026 Redouane Yagouti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Redouane Yagouti
-/
module

public import AlphaRAR.YDK2026.Revised.ComponentwiseCLT
public import AlphaRAR.YDK2026.ResponseConsistency
public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Gaussian.Projection

/-!
# Lemma 5.7 of the revised paper: asymptotic calibration of the Pearson test

Paper (`lem:pearson`): consider `K` Bernoulli arms and a RAR procedure such that, for every `k`,
there is a deterministic positive sequence `c_{n,k} → ∞` with `N_{n,k}/c_{n,k} → 1` a.s. Let
`S_{n,k} = N_{n,k} θ̂_{n,k}` and `θ̃_n = ∑_k (N_{n,k}/n) θ̂_{n,k}`. Under
`H₀ : θ_1 = ⋯ = θ_K = θ` with `0 < θ < 1`,
`𝒳_n = ∑_k (S_{n,k} - N_{n,k} θ̃_n)² / (N_{n,k} θ̃_n (1 - θ̃_n)) ⇒ χ²_{K-1}`.

Encoding:
* Bernoulli arms under `H₀`: every `ν k` is `Ber(1, 0, θ)`, mass `θ` at `1` and `1 - θ` at `0`;
* `θ̂_{n,k}` is the paper's estimator (1), `estimator`, with initial values `θ₀`;
* `χ²_{K-1}` is Tau Ceti's `chiSquaredMeasure (K - 1)`;
* a division by zero in `𝒳_n` gives `0` in Lean; it happens with probability tending to `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning TauCeti.Probability Real

open scoped Topology InnerProductSpace

namespace AlphaRAR.Revised

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- The pooled estimate `θ̃_n = ∑_k (N_{n,k}/n) θ̂_{n,k}`. -/
noncomputable def pooledEstimate (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k, (pullCount A k n ω : ℝ) / n
    * estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n

/-- The Pearson statistic
`𝒳_n = ∑_k (S_{n,k} - N_{n,k} θ̃_n)² / (N_{n,k} θ̃_n (1 - θ̃_n))`,
with `S_{n,k} = N_{n,k} θ̂_{n,k}`. -/
noncomputable def pearsonStat (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ) (n : ℕ) (ω : Ω) :
    ℝ :=
  ∑ k, ((pullCount A k n ω : ℝ)
      * estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n
      - (pullCount A k n ω : ℝ) * pooledEstimate A Y θ₀ n ω) ^ 2
    / ((pullCount A k n ω : ℝ) * pooledEstimate A Y θ₀ n ω * (1 - pooledEstimate A Y θ₀ n ω))


/-! ### The projection `I - s sᵀ` and the chi-square law -/

/-- `z ↦ z - ⟨s, z⟩ s`, the projection `I - s sᵀ` of the paper. -/
noncomputable def projOff (s z : EuclideanSpace ℝ 𝓐) : EuclideanSpace ℝ 𝓐 := z - ⟪s, z⟫_ℝ • s

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
lemma continuous_normSq_projOff :
    Continuous fun p : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 ↦ ‖projOff p.2 p.1‖ ^ 2 := by
  have h : Continuous fun p : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 ↦
      p.1 - ⟪p.2, p.1⟫_ℝ • p.2 :=
    continuous_fst.sub ((Continuous.inner (𝕜 := ℝ) continuous_snd continuous_fst).smul
      continuous_snd)
  exact h.norm.pow 2

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
/-- For a unit vector `s`, `‖(I - s sᵀ) G‖² ∼ χ²_{K-1}` when `G` is a standard Gaussian. -/
lemma stdGaussian_map_projOff [Nonempty 𝓐] (s : EuclideanSpace ℝ 𝓐) (hs : ‖s‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ 𝓐)).map (fun x ↦ ‖projOff s x‖ ^ 2)
      = chiSquaredMeasure ((Fintype.card 𝓐 : ℝ) - 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hproj : (fun x ↦ ‖projOff s x‖ ^ 2)
      = fun x ↦ ‖(ℝ ∙ s)ᗮ.starProjection x‖ ^ 2 := by
    funext x
    rw [Submodule.starProjection_orthogonal]
    simp [projOff, Submodule.starProjection_singleton, hs]
  rw [hproj, Submodule.map_norm_sq_starProjection_stdGaussian,
    Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one hs0, finrank_euclideanSpace,
    Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-! ### Bernoulli arms -/

lemma integral_id_bernoulli (θ : unitInterval) :
    ∫ x, x ∂(bernoulliMeasure (1 : ℝ) 0 θ) = (θ : ℝ) := by
  rw [integral_bernoulliMeasure]
  simp

lemma variance_id_bernoulli (θ : unitInterval) :
    Var[id; bernoulliMeasure (1 : ℝ) 0 θ] = (θ : ℝ) * (1 - θ) := by
  have hm : (bernoulliMeasure (1 : ℝ) 0 θ)[id] = (θ : ℝ) := integral_id_bernoulli θ
  rw [variance_eq_integral measurable_id.aemeasurable, hm, integral_bernoulliMeasure]
  simp only [id, smul_eq_mul]
  ring

lemma memLp_id_bernoulli (θ : unitInterval) : MemLp id 2 (bernoulliMeasure (1 : ℝ) 0 θ) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
    (integrable_bernoulliMeasure _ _ _ _)

/-! ### Two real-variable facts -/

lemma abs_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |√a - √b| ≤ √|a - b| := by
  rw [← sqrt_sq (abs_nonneg (√a - √b))]
  refine sqrt_le_sqrt ?_
  have hx : |√a - √b| ≤ √a + √b :=
    abs_sub_le_iff.mpr ⟨by linarith [sqrt_nonneg b], by linarith [sqrt_nonneg a]⟩
  have hab : |a - b| = |√a - √b| * (√a + √b) := by
    rw [← abs_of_nonneg (add_nonneg (sqrt_nonneg a) (sqrt_nonneg b)), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt ha, sq_sqrt hb]
  rw [hab, sq]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
/-- **The algebra of the Pearson statistic**: with `t = ∑_k (N_k/n) e_k` and `∑_k N_k = n`,
`∑_k (N_k e_k - N_k t)² / (N_k t (1-t)) = ‖(I - s sᵀ) z‖² σ² / (t (1-t))`, where
`z_k = √N_k (e_k - θ)/σ` and `s_k = √(N_k/n)`. -/
lemma pearson_algebra (N e : 𝓐 → ℝ) (hN : ∀ k, 0 ≤ N k) {n : ℝ} (hn : 0 < n)
    (hsum : ∑ k, N k = n) (θ σ : ℝ) (hσ : 0 < σ) :
    ∑ k, (N k * e k - N k * ∑ j, N j / n * e j) ^ 2
        / (N k * (∑ j, N j / n * e j) * (1 - ∑ j, N j / n * e j))
      = (∑ k, (σ⁻¹ * (√(N k) * (e k - θ))
          - (∑ j, σ⁻¹ * (√(N j) * (e j - θ)) * √(N j / n)) * √(N k / n)) ^ 2)
        * (σ ^ 2 / ((∑ j, N j / n * e j) * (1 - ∑ j, N j / n * e j))) := by
  set t := ∑ j, N j / n * e j with ht
  set D := t * (1 - t) with hD
  have hNe : ∑ j, N j * (e j - θ) = n * (t - θ) := by
    have h1 : ∑ j, N j * e j = n * t := by
      rw [ht, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by field_simp
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, h1]
  have hsq : ∀ j, √(N j / n) * √(N j) = N j / √n := fun j ↦ by
    rw [sqrt_div' _ hn.le, div_mul_eq_mul_div, mul_self_sqrt (hN j)]
  have hin : ∑ j, σ⁻¹ * (√(N j) * (e j - θ)) * √(N j / n) = σ⁻¹ * √n * (t - θ) := by
    calc ∑ j, σ⁻¹ * (√(N j) * (e j - θ)) * √(N j / n)
        = σ⁻¹ / √n * ∑ j, N j * (e j - θ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [show σ⁻¹ * (√(N j) * (e j - θ)) * √(N j / n)
            = σ⁻¹ * (√(N j / n) * √(N j)) * (e j - θ) by ring, hsq]
          ring
      _ = σ⁻¹ * √n * (t - θ) := by
          rw [hNe]
          have hsn : √n ≠ 0 := (sqrt_pos.mpr hn).ne'
          field_simp
          rw [sq_sqrt hn.le]
  rw [hin, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hnk : √n * √(N k / n) = √(N k) := by
    rw [← sqrt_mul hn.le, mul_div_cancel₀ _ hn.ne']
  have hcomp : σ⁻¹ * (√(N k) * (e k - θ)) - σ⁻¹ * √n * (t - θ) * √(N k / n)
      = σ⁻¹ * √(N k) * (e k - t) := by
    rw [show σ⁻¹ * √n * (t - θ) * √(N k / n) = σ⁻¹ * (√n * √(N k / n)) * (t - θ) by ring, hnk]
    ring
  rw [hcomp]
  have hden : N k * t * (1 - t) = N k * D := by rw [hD]; ring
  rw [hden]
  by_cases hD0 : D = 0
  · simp [hD0]
  by_cases hNk : N k = 0
  · simp [hNk]
  have hσ0 : σ ≠ 0 := hσ.ne'
  rw [mul_pow, mul_pow, sq_sqrt (hN k)]
  field_simp

variable (𝓐) in
/-- `χ²_{K-1}` is a probability measure, as `K ≥ 1`. -/
instance isProbabilityMeasure_chiSquaredMeasure_card_sub_one [Nonempty 𝓐] :
    IsProbabilityMeasure (chiSquaredMeasure ((Fintype.card 𝓐 : ℝ) - 1)) :=
  isProbabilityMeasure_chiSquaredMeasure (by
    have : (1 : ℝ) ≤ Fintype.card 𝓐 := by exact_mod_cast Fintype.card_pos
    linarith)

/-! ### The ingredients of the proof -/

omit [Fintype 𝓐] [IsProbabilityMeasure P] in
lemma measurable_pooledEstimate [Fintype 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ) (n : ℕ) :
    Measurable (pooledEstimate A Y θ₀ n) :=
  Finset.measurable_sum _ fun k _ ↦ ((measurable_pullCount_real h k n).div_const _).mul
    (measurable_estimator_apply h k (θ₀ k) n)

omit [IsProbabilityMeasure P] in
lemma measurable_pearsonStat (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (θ₀ : 𝓐 → ℝ) (n : ℕ) : Measurable (pearsonStat A Y θ₀ n) := by
  have hN := measurable_pullCount_real h
  have ht := measurable_pooledEstimate h θ₀ n
  exact Finset.measurable_sum _ fun k _ ↦
    ((((hN k n).mul (measurable_estimator_apply h k (θ₀ k) n)).sub ((hN k n).mul ht)).pow_const
      2).div (((hN k n).mul ht).mul (measurable_const.sub ht))

/-- The normalized estimator errors `Z_n = (√N_{n,k} (θ̂_{n,k} - θ_k) / σ)_k`. -/
noncomputable def pearsonZ (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (σ : ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  σ⁻¹ • WithLp.toLp 2 fun k ↦ √(pullCount A k n ω : ℝ)
    * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)

omit [Fintype 𝓐] in
/-- The square roots of the allocation proportions, `s_n = (√(N_{n,k}/n))_k`. -/
noncomputable def propSqrt (A : ℕ → Ω → 𝓐) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 fun k ↦ √((pullCount A k n ω : ℝ) / n)

omit [DecidableEq 𝓐] in
/-- Their deterministic counterpart, `s̄_n = (√(c_{n,k} / ∑_j c_{n,j}))_k`. -/
noncomputable def targetSqrt (c : 𝓐 → ℕ → ℝ) (n : ℕ) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 fun k ↦ √(c k n / ∑ j, c j n)

omit [Fintype 𝓐] [IsProbabilityMeasure P] in
lemma measurable_propSqrt (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ) :
    Measurable (propSqrt (𝓐 := 𝓐) A n) :=
  (WithLp.measurable_toLp 2 _).comp
    (Measurable.of_eval fun k ↦ ((measurable_pullCount_real h k n).div_const _).sqrt)

omit [Fintype 𝓐] [IsProbabilityMeasure P] in
lemma measurable_pearsonZ [Finite 𝓐] (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (θ₀ : 𝓐 → ℝ) (σ : ℝ) (n : ℕ) : Measurable (pearsonZ ν A Y θ₀ σ n) := by
  cases nonempty_fintype 𝓐
  have hv : Measurable fun ω ↦ (WithLp.toLp 2 fun k ↦ √(pullCount A k n ω : ℝ)
      * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)
        : EuclideanSpace ℝ 𝓐) :=
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun k ↦
      (measurable_pullCount_real h k n).sqrt.mul
        ((measurable_estimator_apply h k (θ₀ k) n).sub_const (ν.means k)))
  exact (continuous_const_smul σ⁻¹).measurable.comp hv

omit [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] in
lemma norm_targetSqrt [Nonempty 𝓐] {c : 𝓐 → ℕ → ℝ} (hcpos : ∀ k n, 0 < c k n) (n : ℕ) :
    ‖targetSqrt c n‖ = 1 := by
  have hC : 0 < ∑ j, c j n := Finset.sum_pos (fun j _ ↦ hcpos j n) Finset.univ_nonempty
  rw [EuclideanSpace.norm_eq]
  simp only [targetSqrt, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs,
    sq_sqrt (div_nonneg (hcpos _ n).le hC.le)]
  rw [← Finset.sum_div, div_self hC.ne', sqrt_one]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel ν] [IsProbabilityMeasure P] in
/-- The identity `𝒳_n = ‖(I - s_n s_nᵀ) Z_n‖² σ² / (θ̃_n (1 - θ̃_n))`, for `n ≥ 1`. -/
lemma pearsonStat_eq {θ : ℝ} (hmean : ∀ k, ν.means k = θ) {σ : ℝ} (hσ : 0 < σ) {n : ℕ}
    (hn : 0 < n) (θ₀ : 𝓐 → ℝ) (ω : Ω) :
    pearsonStat A Y θ₀ n ω = ‖projOff (propSqrt A n ω) (pearsonZ ν A Y θ₀ σ n ω)‖ ^ 2
      * (σ ^ 2 / (pooledEstimate A Y θ₀ n ω * (1 - pooledEstimate A Y θ₀ n ω))) := by
  have hsum : ∑ k, (pullCount A k n ω : ℝ) = n := by
    rw [← Nat.cast_sum, sum_pullCount]
  have halg := pearson_algebra (fun k ↦ (pullCount A k n ω : ℝ))
    (fun k ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n)
    (fun k ↦ Nat.cast_nonneg _) (Nat.cast_pos.mpr hn) hsum θ σ hσ
  rw [EuclideanSpace.norm_sq_eq]
  simp only [projOff, pearsonZ, propSqrt, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs, hmean]
  simp only [pearsonStat, pooledEstimate]
  rw [halg]

/-- A centred Gaussian with covariance `σ² I`, scaled by `σ⁻¹`, is standard. -/
lemma multivariateGaussian_diagonal_const_map_smul {σ : ℝ} (hσ : 0 < σ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ 𝓐) (Matrix.diagonal fun _ ↦ σ ^ 2)).map
      (fun x ↦ σ⁻¹ • x) = stdGaussian (EuclideanSpace ℝ 𝓐) := by
  have hmap := multivariateGaussian_map_matrix (Matrix.diagonal fun _ : 𝓐 ↦ σ ^ 2)
    (σ⁻¹ • (1 : Matrix 𝓐 𝓐 ℝ)) (Matrix.PosSemidef.diagonal fun _ ↦ sq_nonneg σ)
  have hf : (fun x : EuclideanSpace ℝ 𝓐 ↦
      (WithLp.toLp 2 ((σ⁻¹ • (1 : Matrix 𝓐 𝓐 ℝ)).mulVec (WithLp.ofLp x))
        : EuclideanSpace ℝ 𝓐)) = fun x ↦ σ⁻¹ • x := by
    funext x
    simp [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcov : σ⁻¹ • (1 : Matrix 𝓐 𝓐 ℝ) * Matrix.diagonal (fun _ ↦ σ ^ 2)
      * (σ⁻¹ • (1 : Matrix 𝓐 𝓐 ℝ)).transpose = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
      field_simp
    · simp [hij]
  rw [hf, hcov, multivariateGaussian_zero_one] at hmap
  exact hmap

/-- Under `H₀`, `Z_n ⇒ 𝒩(0, I)` (Lemma 4.5). -/
lemma pearsonZ_tendsto (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ)
    (θ : unitInterval) (hθ0 : 0 < (θ : ℝ)) (hθ1 : (θ : ℝ) < 1)
    (hH0 : ∀ k, ν k = bernoulliMeasure (1 : ℝ) 0 θ)
    (c : 𝓐 → ℕ → ℝ) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    TendstoInDistribution (pearsonZ ν A Y θ₀ √((θ : ℝ) * (1 - θ))) atTop id (fun _ ↦ P)
      (stdGaussian (EuclideanSpace ℝ 𝓐)) := by
  set σ := √((θ : ℝ) * (1 - θ)) with hσdef
  have hpos : 0 < (θ : ℝ) * (1 - θ) := mul_pos hθ0 (by linarith)
  have hσ : 0 < σ := sqrt_pos.mpr hpos
  have hA : ∀ k, MemLp id 2 (ν k) := fun k ↦ hH0 k ▸ memLp_id_bernoulli θ
  have hvar : (fun k ↦ Var[id; ν k]) = fun _ ↦ σ ^ 2 := by
    funext k
    rw [hH0, variance_id_bernoulli, hσdef, sq_sqrt hpos.le]
  have h45 := componentwise_clt h θ₀ hA c hc hNc
  rw [hvar] at h45
  have hcomp := h45.continuous_comp (g := fun x : EuclideanSpace ℝ 𝓐 ↦ σ⁻¹ • x) (by fun_prop)
  have hlaw : HasLaw (fun x : EuclideanSpace ℝ 𝓐 ↦ σ⁻¹ • x) (stdGaussian (EuclideanSpace ℝ 𝓐))
      (multivariateGaussian 0 (Matrix.diagonal fun _ ↦ σ ^ 2)) :=
    ⟨(continuous_const_smul σ⁻¹).measurable.aemeasurable,
      multivariateGaussian_diagonal_const_map_smul hσ⟩
  exact (tendstoInDistribution_id_iff hlaw).mpr hcomp

omit [MeasurableSingletonClass 𝓐] [Fintype 𝓐] in
lemma pullCount_tendsto_atTop {c : 𝓐 → ℕ → ℝ} (hcpos : ∀ k n, 0 < c k n)
    (hc : ∀ k, Tendsto (c k) atTop atTop) {ω : Ω} {k : 𝓐}
    (hω : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    Tendsto (fun n ↦ (pullCount A k n ω : ℝ)) atTop atTop :=
  (hω.pos_mul_atTop one_pos (hc k)).congr fun n ↦ by
    have := (hcpos k n).ne'
    field_simp

/-- Under `H₀`, the pooled estimate is consistent: `θ̃_n → θ` a.s. -/
lemma pooledEstimate_tendsto (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (θ₀ : 𝓐 → ℝ) {θ : ℝ} (hmean : ∀ k, ν.means k = θ) (hA : ∀ k, MemLp id 2 (ν k))
    {c : 𝓐 → ℕ → ℝ} (hcpos : ∀ k n, 0 < c k n) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ pooledEstimate A Y θ₀ n ω) atTop (𝓝 θ) := by
  filter_upwards [ae_all_iff.mpr fun k ↦ estimator_ae_tendsto_of_pullCount_atTop h k hA (θ₀ k),
    ae_all_iff.mpr hNc] with ω hest hω
  have he : ∀ k, Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n)
      atTop (𝓝 θ) := fun k ↦ by
    simpa [hmean k] using hest k (pullCount_tendsto_atTop hcpos hc (hω k))
  have h0 : ∀ k, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / n
      * (estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - θ)) atTop (𝓝 0) :=
    fun k ↦ by
      refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using ((he k).sub_const θ).norm)
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by exact_mod_cast pullCount_le k n ω) (Nat.cast_nonneg _)
  have hs := (tendsto_finsetSum Finset.univ fun k _ ↦ h0 k).add_const θ
  rw [Finset.sum_const_zero, zero_add] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hsum1 : ∑ k, (pullCount A k n ω : ℝ) / n = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_pullCount, div_self (by positivity)]
  simp only [pooledEstimate, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
  ring

omit [MeasurableSingletonClass 𝓐] [IsProbabilityMeasure P] in
/-- `s_n - s̄_n → 0` a.s.: the proportions follow the deterministic scales. -/
lemma propSqrt_sub_targetSqrt [Nonempty 𝓐] {c : 𝓐 → ℕ → ℝ} (hcpos : ∀ k n, 0 < c k n)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ propSqrt A n ω - targetSqrt c n) atTop (𝓝 0) := by
  filter_upwards [ae_all_iff.mpr hNc] with ω hω
  have hC : ∀ n, 0 < ∑ j, c j n := fun n ↦
    Finset.sum_pos (fun j _ ↦ hcpos j n) Finset.univ_nonempty
  -- `n / ∑_j c_{n,j} → 1`, a weighted average of the `N_{n,j}/c_{n,j}`.
  have hnC : Tendsto (fun n : ℕ ↦ (n : ℝ) / ∑ j, c j n) atTop (𝓝 1) := by
    have hbound : ∀ n : ℕ, ‖(n : ℝ) / ∑ j, c j n - 1‖
        ≤ ∑ j, |(pullCount A j n ω : ℝ) / c j n - 1| := fun n ↦ by
      have heq : (n : ℝ) / ∑ j, c j n - 1
          = ∑ j, ((pullCount A j n ω : ℝ) / c j n - 1) * (c j n / ∑ i, c i n) := by
        have hsum : ∑ k, (pullCount A k n ω : ℝ) = n := by rw [← Nat.cast_sum, sum_pullCount]
        have h1 : ∀ j, ((pullCount A j n ω : ℝ) / c j n - 1) * (c j n / ∑ i, c i n)
            = (pullCount A j n ω : ℝ) / ∑ i, c i n - c j n / ∑ i, c i n := fun j ↦ by
          have := (hcpos j n).ne'
          have := (hC n).ne'
          field_simp
        rw [Finset.sum_congr rfl fun j _ ↦ h1 j, Finset.sum_sub_distrib, ← Finset.sum_div,
          ← Finset.sum_div, hsum, div_self (hC n).ne']
      rw [heq, Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_of_nonneg (div_nonneg (hcpos j n).le (hC n).le)]
      exact div_le_one_of_le₀ (Finset.single_le_sum (fun i _ ↦ (hcpos i n).le)
        (Finset.mem_univ j)) (hC n).le
    have hz : Tendsto (fun n ↦ ∑ j, |(pullCount A j n ω : ℝ) / c j n - 1|) atTop (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ fun j _ ↦ ((hω j).sub_const 1).abs
      simpa using this
    have := squeeze_zero_norm hbound hz
    simpa using this.add_const 1
  -- Componentwise.
  have hcomp : ∀ k, Tendsto (fun n ↦ √((pullCount A k n ω : ℝ) / n) - √(c k n / ∑ j, c j n))
      atTop (𝓝 0) := fun k ↦ by
    have hr : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n * ((∑ j, c j n) / n)) atTop
        (𝓝 1) := by
      have := (hω k).mul (hnC.inv₀ one_ne_zero)
      rw [inv_one, mul_one] at this
      exact this.congr fun n ↦ by rw [inv_div]
    have hdiff : Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / n - c k n / ∑ j, c j n) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using (hr.sub_const 1).norm)
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have heq : (pullCount A k n ω : ℝ) / n - c k n / ∑ j, c j n
          = (c k n / ∑ j, c j n) * ((pullCount A k n ω : ℝ) / c k n * ((∑ j, c j n) / n) - 1) := by
        have := (hcpos k n).ne'
        have := (hC n).ne'
        field_simp
      rw [heq, norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hcpos k n).le (hC n).le)]
      exact div_le_one_of_le₀ (Finset.single_le_sum (fun i _ ↦ (hcpos i n).le)
        (Finset.mem_univ k)) (hC n).le
    have hsq : Tendsto (fun n ↦ √|(pullCount A k n ω : ℝ) / n - c k n / ∑ j, c j n|) atTop
        (𝓝 0) := by
      have habs : Tendsto (fun n ↦ |(pullCount A k n ω : ℝ) / n - c k n / ∑ j, c j n|) atTop
          (𝓝 0) := by simpa using hdiff.abs
      have := (continuous_sqrt.tendsto 0).comp habs
      rw [sqrt_zero] at this
      exact this
    refine squeeze_zero_norm (fun n ↦ ?_) hsq
    rw [Real.norm_eq_abs]
    exact abs_sqrt_sub_sqrt_le (by positivity) (div_nonneg (hcpos k n).le (hC n).le)
  have hvec := ((PiLp.continuous_toLp 2 fun _ : 𝓐 ↦ ℝ).tendsto 0).comp
    (tendsto_pi_nhds.mpr hcomp)
  rw [WithLp.toLp_zero] at hvec
  have hfun : (fun n ↦ propSqrt A n ω - targetSqrt c n) = WithLp.toLp 2 ∘ fun n k ↦
      √((pullCount A k n ω : ℝ) / n) - √(c k n / ∑ j, c j n) := by
    funext n
    ext k
    simp [propSqrt, targetSqrt]
  rw [hfun]
  exact hvec

/-- **Lemma 5.7** (revised paper), the Pearson statistic is asymptotically `χ²_{K-1}` under the
null hypothesis of equal Bernoulli means.

Proof, as in the paper, but with the Skorokhod representation replaced by the subsequence
criterion: along any subsequence, the deterministic unit vectors `s̄_n` have a further
subsequence converging to some unit `s`; along it Slutsky gives
`𝒳_n ⇒ ‖(I - s sᵀ) G‖² ∼ χ²_{K-1}`, whatever `s`. -/
theorem pearsonStat_tendsto_chiSquared [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (θ₀ : 𝓐 → ℝ)
    (θ : unitInterval) (hθ0 : 0 < (θ : ℝ)) (hθ1 : (θ : ℝ) < 1)
    (hH0 : ∀ k, ν k = bernoulliMeasure (1 : ℝ) 0 θ)
    (c : 𝓐 → ℕ → ℝ) (hcpos : ∀ k n, 0 < c k n) (hc : ∀ k, Tendsto (c k) atTop atTop)
    (hNc : ∀ k, ∀ᵐ ω ∂P, Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / c k n) atTop (𝓝 1)) :
    TendstoInDistribution (fun n ω ↦ pearsonStat A Y θ₀ n ω) atTop id (fun _ ↦ P)
      (chiSquaredMeasure ((Fintype.card 𝓐 : ℝ) - 1)) := by
  set σ := √((θ : ℝ) * (1 - θ)) with hσdef
  have hpos : 0 < (θ : ℝ) * (1 - θ) := mul_pos hθ0 (by linarith)
  have hσ : 0 < σ := sqrt_pos.mpr hpos
  have hmean : ∀ k, ν.means k = θ := fun k ↦ by
    rw [Kernel.means_apply, hH0]
    exact integral_id_bernoulli θ
  have hA : ∀ k, MemLp id 2 (ν k) := fun k ↦ hH0 k ▸ memLp_id_bernoulli θ
  have hZ := pearsonZ_tendsto h θ₀ θ hθ0 hθ1 hH0 c hc hNc
  -- The variance ratio `σ² / (θ̃_n (1 - θ̃_n)) → 1` a.s.
  set R : ℕ → Ω → ℝ := fun n ω ↦
    σ ^ 2 / (pooledEstimate A Y θ₀ n ω * (1 - pooledEstimate A Y θ₀ n ω)) with hRdef
  have hR : ∀ᵐ ω ∂P, Tendsto (fun n ↦ R n ω) atTop (𝓝 1) := by
    filter_upwards [pooledEstimate_tendsto h θ₀ hmean hA hcpos hc hNc] with ω hω
    have h2 : Tendsto (fun n ↦ σ ^ 2 / (pooledEstimate A Y θ₀ n ω
        * (1 - pooledEstimate A Y θ₀ n ω))) atTop (𝓝 (σ ^ 2 / ((θ : ℝ) * (1 - θ)))) :=
      tendsto_const_nhds.div (hω.mul (tendsto_const_nhds.sub hω)) hpos.ne'
    have hlim : σ ^ 2 / ((θ : ℝ) * (1 - θ)) = 1 := by
      rw [hσdef, sq_sqrt hpos.le, div_self hpos.ne']
    rw [hlim] at h2
    exact h2
  have hRmeas : ∀ n, Measurable (R n) := fun n ↦
    measurable_const.div ((measurable_pooledEstimate h θ₀ n).mul
      (measurable_const.sub (measurable_pooledEstimate h θ₀ n)))
  have hsv := propSqrt_sub_targetSqrt hcpos hNc
  refine ⟨fun n ↦ (measurable_pearsonStat h θ₀ n).aemeasurable, aemeasurable_id, ?_⟩
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨s, hs, φ, hφ, hφlim⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ 𝓐) 1).tendsto_subseq
    (x := fun m ↦ targetSqrt c (ns m)) fun m ↦ by simp [norm_targetSqrt hcpos]
  refine ⟨φ, ?_⟩
  have hms : Tendsto (fun m ↦ ns (φ m)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hZs : TendstoInDistribution (fun m ↦ pearsonZ ν A Y θ₀ σ (ns (φ m))) atTop id
      (fun _ ↦ P) (stdGaussian (EuclideanSpace ℝ 𝓐)) := hZ.comp hms
  have hsvs : TendstoInMeasure P (fun m ↦ propSqrt A (ns (φ m))) atTop (fun _ ↦ s) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun m ↦ (measurable_propSqrt h _).aestronglyMeasurable) ?_
    filter_upwards [hsv] with ω hω
    have := (hω.comp hms).add hφlim
    rw [zero_add] at this
    exact this.congr fun m ↦ sub_add_cancel _ _
  have hq : TendstoInDistribution (fun m ω ↦ ‖projOff (propSqrt A (ns (φ m)) ω)
        (pearsonZ ν A Y θ₀ σ (ns (φ m)) ω)‖ ^ 2) atTop (fun x ↦ ‖projOff s (id x)‖ ^ 2)
      (fun _ ↦ P) (stdGaussian (EuclideanSpace ℝ 𝓐)) :=
    TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : EuclideanSpace ℝ 𝓐 × EuclideanSpace ℝ 𝓐 ↦ ‖projOff p.2 p.1‖ ^ 2)
      (X := fun m ↦ pearsonZ ν A Y θ₀ σ (ns (φ m))) (Y := fun m ↦ propSqrt A (ns (φ m)))
      (c := s) continuous_normSq_projOff hZs hsvs fun m ↦ (measurable_propSqrt h _).aemeasurable
  have hRs : TendstoInMeasure P (fun m ↦ R (ns (φ m))) atTop (fun _ ↦ 1) :=
    tendstoInMeasure_of_tendsto_ae (fun m ↦ (hRmeas _).aestronglyMeasurable)
      (by filter_upwards [hR] with ω hω using hω.comp hms)
  have hprod := hq.mul_of_tendstoInMeasure_const hRs fun m ↦ (hRmeas _).aemeasurable
  have hlaw : HasLaw (fun x : EuclideanSpace ℝ 𝓐 ↦ ‖projOff s (id x)‖ ^ 2 * 1)
      (chiSquaredMeasure ((Fintype.card 𝓐 : ℝ) - 1)) (stdGaussian (EuclideanSpace ℝ 𝓐)) :=
    ⟨((continuous_normSq_projOff.comp (continuous_id.prodMk continuous_const)).mul
        continuous_const).measurable.aemeasurable,
      by simpa using stdGaussian_map_projOff s (by simpa using hs)⟩
  have hfin := (tendstoInDistribution_id_iff hlaw).mpr (hprod.congr'
    (by
      filter_upwards [hms.eventually_gt_atTop 0] with m hm
      exact ae_of_all _ fun ω ↦ (pearsonStat_eq hmean hσ hm θ₀ ω).symm)
    EventuallyEq.rfl fun m ↦ (measurable_pearsonStat h θ₀ _).aemeasurable)
  exact hfin.tendsto

end AlphaRAR.Revised
