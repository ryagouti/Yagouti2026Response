/-
Copyright (c) 2026 Redouane Yagouti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Redouane Yagouti
-/
module

public import AlphaRAR.YDK2026.ForcedExplorationSparse

/-!
# Lemma 5.4 of the revised paper: sparse-arm allocation

Paper (`lem:sparse-allocation`): for an αRTS-FE design satisfying Conditions A and C, every
treatment `k` with `v_k = 0` has `N_{n,k} / h(n) → 1` a.s.

Condition C (the revised paper, Section 5.2):
* `ρ` is continuous at `Θ`; on some open neighbourhood `𝒰` of `Θ`, `ρ_k ∈ C²(𝒰)` and `ρ_k ≥ 0`
  for every `k` with `v_k = 0`;
* `√(n log log n) = o(h(n))` and `h(n - K⌈h(n)⌉ - 1) ∼ h(n)`.

Encoding: as in `Revised/SparseRate.lean`. A set in `𝓝 Θ` contains an open neighbourhood of `Θ`,
so `∃ U ∈ 𝓝 Θ` is the paper's "on some open neighbourhood".

`ρ` continuous at `Θ` is part of Condition C, as in the paper. Difference from the paper: `T` is
also assumed measurable (`hTm`), which the paper leaves implicit (the plug-in targets must be random
variables). The paper's `h ≥ 0` is not needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Real Asymptotics

open scoped Topology

namespace AlphaRAR.Revised

variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓐] [Fintype 𝓐] [DecidableEq 𝓐]
  {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- **Condition C** of the revised paper, on the target function `T` (the paper's `ρ`) at
`Θ = ν.means` and the exploration function `hsched` (the paper's `h`). -/
structure ConditionC (ν : Kernel 𝓐 ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (hsched : ℕ → ℝ) : Prop where
  /-- `ρ` is continuous at `Θ`. -/
  continuousAt : ContinuousAt T ν.means
  /-- Near `Θ`, every sparse coordinate `ρ_k` is `C²` and nonnegative. -/
  sparse_contDiff : ∀ k, T ν.means k = 0 →
    ∃ U ∈ 𝓝 ν.means, ContDiffOn ℝ 2 (fun z ↦ T z k) U ∧ ∀ z ∈ U, 0 ≤ T z k
  /-- `√(n log log n) = o(h(n))`. -/
  sqrt_loglog_isLittleO :
    (fun n : ℕ ↦ √((n : ℝ) * log (log (n : ℝ)))) =o[atTop] hsched
  /-- `h(n - K⌈h(n)⌉ - 1) ∼ h(n)`. -/
  shift_isEquivalent :
    (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1))) ~[atTop] hsched

variable [StandardBorelSpace 𝓐] [Nonempty 𝓐]

/-- **Lemma 5.4** (revised paper), sparse-arm allocation: under Conditions A and C, every arm
with `v_k = 0` is sampled `∼ h(n)` times. -/
theorem sparse_allocation
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) (θ₀ : 𝓐 → ℝ) {T : (𝓐 → ℝ) → 𝓐 → ℝ}
    (hTm : Measurable T) (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    (hC : ConditionC ν T hsched)
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) (hARTSFE : IsARTSFE alg θ₀ T hsched α) :
    ∀ᵐ ω ∂P, ∀ k, T ν.means k = 0 →
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / hsched n) atTop (𝓝 1) := by
  -- Condition C, in the form the existing proof uses.
  have hspos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < hsched n := hh.tendsto_atTop.eventually_gt_atTop 0
  have hshift : Tendsto
      (fun n ↦ hsched (n - (Fintype.card 𝓐 * ⌈hsched n⌉₊ + 1)) / hsched n) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hspos.mono fun _ hn ↦ hn.ne')).mp hC.shift_isEquivalent
  have hstar : Tendsto (fun m : ℕ ↦ (m : ℝ) * log (log m) / (hsched m * hsched m))
      atTop (𝓝 0) := by
    have hsq := hC.sqrt_loglog_isLittleO.tendsto_div_nhds_zero.pow 2
    rw [zero_pow two_ne_zero] at hsq
    refine hsq.congr' ?_
    have hlog1 : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ log m :=
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    filter_upwards [hlog1] with m hm
    rw [div_pow, sq_sqrt (mul_nonneg (Nat.cast_nonneg m) (log_nonneg hm)), sq]
  have hT2 : ∀ a, T ν.means a = 0 → ContDiffAt ℝ 2 (T · a) ν.means := fun a ha ↦ by
    obtain ⟨U, hU, hcd, -⟩ := hC.sparse_contDiff a ha
    exact hcd.contDiffAt hU
  -- Sparse arms are eventually fed only by forced exploration, which sets their scale to `h(n)`.
  filter_upwards [fe_of_isARTSFE h hARTSFE,
    aRTSFE_fEfed_of_contDiffAt h θ₀ hA hh hshift hstar hTm hC.continuousAt hTnn hTsum
      ⟨hα.1, hα.2.le⟩ hARTSFE
      hT2] with ω hfe hFE k hk
  obtain ⟨n₀, E, hEmono, hEstep, hEsmall⟩ := hFE k hk
  exact pullCount_div_sched_tendsto_one ω hh hfe hshift (n₀ := n₀) E hEmono hEstep hEsmall

end AlphaRAR.Revised
