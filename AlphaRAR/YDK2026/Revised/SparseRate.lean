/-
Copyright (c) 2026 Redouane Yagouti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Redouane Yagouti
-/
module

public import AlphaRAR.YDK2026.ForcedExplorationSparse

/-!
# Theorem 5.3 of the revised paper: consistency and rate for possibly sparse targets

Paper (`thm:sparse-rate`): under Condition A and assuming that `ρ` is continuous at `Θ`, αRTS-FE
satisfies, for all `k`, `N_{n,k} → ∞`, `N_{n,k}/n → v_k` and
`θ̂_{n,k} - θ_k = O(√(log log N_{n,k} / N_{n,k}))` a.s. Moreover
`‖Θ̂_n - Θ‖ = O(√(log log n / h(n - K⌈h(n)⌉ - 1)))` a.s.

Encoding:
* Condition A: `MemLp id 2 (ν k)`;
* `ρ` continuous at `Θ` (`ContinuousAt T ν.means`), as in the paper;
* Definition 5.1: `h` non-decreasing, `h → ∞`, `h = o(n)`; `IsARTSFE` with `α ∈ [0, 1)`; the
  paper's `h ≥ 0` is not needed;
* `n - K⌈h(n)⌉ - 1` is the truncated subtraction of `ℕ`, which agrees with the paper for large `n`;
* the norm on `𝓐 → ℝ` is the sup norm (all norms on `ℝ^K` are equivalent).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real

open scoped Topology

namespace AlphaRAR.Revised

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- **Theorem 5.3** (revised paper), consistency and rate of αRTS-FE for possibly sparse targets. -/
theorem aRTSFE_sparse_rate
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    (hTc : ContinuousAt T ν.means) (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) (hARTSFE : IsARTSFE alg θ₀ T hsched α) :
    ∀ᵐ ω ∂P,
      (∀ k,
        Tendsto (fun n ↦ pullCount A k n ω) atTop atTop ∧
        Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (T ν.means k)) ∧
        (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)
          =O[atTop] (fun n ↦ √(log (log (pullCount A k n ω : ℝ)) / (pullCount A k n ω : ℝ)))) ∧
      (fun n ↦ ‖fun k ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n
          - ν.means k‖)
        =O[atTop] (fun n ↦ √(log (log (n : ℝ))
          / hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)))) := by
  -- The catch-up window `W(n) = K⌈h(n)⌉ + 1` is `o(n)`, so `n - W(n) → ∞`, and with it the
  -- deterministic floor `L(n) = h(n - W(n))`.
  have hwin : Tendsto (fun n : ℕ ↦ n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    have hz : Tendsto (fun n : ℕ ↦ ((Fintype.card 𝓐 : ℝ) * (hsched n + 1) + 1) / n)
        atTop (𝓝 0) := by
      have h1 := hh.div_tendsto_zero.add tendsto_one_div_atTop_nhds_zero_nat
      have h2 := (h1.const_mul (Fintype.card 𝓐 : ℝ)).add tendsto_one_div_atTop_nhds_zero_nat
      simp only [add_zero, mul_zero] at h2
      exact h2.congr fun n ↦ by ring
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hz.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_gt_atTop 0, hh.tendsto_atTop.eventually_ge_atTop 0] with n hn hn0 hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_le_iff₀ hnpos] at hn
    have hceil := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one hs).le
      (Nat.cast_nonneg (α := ℝ) (Fintype.card 𝓐))
    have hW : ((Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1 : ℕ) : ℝ) ≤ n / 2 := by
      push_cast
      linarith
    have hWn : Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1 ≤ n := by
      exact_mod_cast hW.trans (by linarith : (n : ℝ) / 2 ≤ n)
    rw [Nat.cast_sub hWn]
    linarith
  have hLtop : Tendsto (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1))) atTop atTop :=
    hh.tendsto_atTop.comp hwin
  -- The per-arm conclusions are the existing sparse-rate theorem.
  have hsr : ∀ᵐ ω ∂P, ∀ k,
      Tendsto (fun n ↦ pullCount A k n ω) atTop atTop ∧
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (T ν.means k)) ∧
      ∃ C' : ℝ, ∀ᶠ n in atTop,
        |estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k|
          ≤ C' * √(log (log (pullCount A k n ω : ℝ)) / (pullCount A k n ω : ℝ)) :=
    ae_all_iff.mpr fun k ↦ aRTSFE_sparse_rate_of_continuousAt h hA θ₀ T hTc hTnn hTsum α
      ⟨hα.1, hα.2.le⟩ hh hARTSFE k
  filter_upwards [hsr, fe_of_isARTSFE h hARTSFE] with ω hω hfe
  refine ⟨fun k ↦ ⟨(hω k).1, (hω k).2.1, ?_⟩, ?_⟩
  · obtain ⟨C', hC'⟩ := (hω k).2.2
    refine Asymptotics.isBigO_iff.mpr ⟨C', ?_⟩
    filter_upwards [hC'] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
    exact hn
  · -- Forced exploration's floor `N_{n,k} ≥ L(n)` turns the `N`-scaled rates into one rate.
    obtain ⟨C, hC⟩ := exists_rate_loglog_of_pullCount_ge ω hLtop
      (fun j ↦ eventually_schedShift_le_pullCount ω hh hfe j) (fun j ↦ (hω j).2.2)
    refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_all.mpr hC] with n hn
    rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
    have hnn := (abs_nonneg _).trans (hn (Classical.arbitrary 𝓐))
    refine (pi_norm_le_iff_of_nonneg hnn).mpr fun j ↦ ?_
    rw [Real.norm_eq_abs]
    exact hn j

end AlphaRAR.Revised
