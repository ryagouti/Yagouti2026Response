/-
Copyright (c) 2026 Redouane Yagouti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Redouane Yagouti
-/
module

public import AlphaRAR.YDK2026.ForcedExploration
public import AlphaRAR.YDK2026.ARTSRates

/-!
# Theorem 5.1 of the revised paper, consistency part

Paper (`thm:forced`): under Conditions A and B, Theorem 4.1 remains valid for every design of the
αRTS-FE family. This file states the conclusion of Theorem 4.1 for αRTS-FE, with the limit of
`N_{n,k}/n` identified as `v_k = ρ_k(Θ)` (revised Appendix B, `lem:generic-two-stage`).

Encoding:
* Condition A: `MemLp id 2 (ν k)`;
* Condition B: as in `AlphaRAR.aRTS_LLN` (Theorem 4.1): `T` positive on the values the estimators
  can take, and differentiable at `Θ`;
* Definition 5.1: `h` non-decreasing, `h → ∞`, `h = o(n)` (`IsExplorationSchedule`; the paper's
  `h ≥ 0` is not needed); the design is `IsARTSFE` with `α ∈ [0, 1)`;
* a target allocation takes values in the simplex (`0 ≤ T`, `∑ T = 1`).
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

/-- **Theorem 5.1** (revised paper), the Theorem 4.1 part: strong consistency with log-log rates
for αRTS-FE under Conditions A and B. -/
theorem aRTSFE_LLN
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hA : ∀ k, MemLp id 2 (ν k)) {θ₀ : 𝓐 → ℝ} {T : (𝓐 → ℝ) → 𝓐 → ℝ} (hT : Continuous T)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (hT_diff : DifferentiableAt ℝ T ν.means)
    {hsched : ℕ → ℝ} (hh : IsExplorationSchedule hsched)
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) (hARTSFE : IsARTSFE alg θ₀ T hsched α) (k : 𝓐) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (pullCount A k n ω : ℝ) / (n : ℝ)) atTop (𝓝 (T ν.means k)) ∧
      Tendsto (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω)
        (Y · ω) (θ₀ k) n) atTop (𝓝 (ν.means k)) ∧
      (fun n ↦ estimator (fun j ↦ actionIndicator A k j ω) (Y · ω) (θ₀ k) n - ν.means k)
          =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) ∧
      (fun n ↦ T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω)
        (Y · ω) (θ₀ k') n) k - T ν.means k)
          =O[atTop] (fun n ↦ √((n : ℝ) * log (log (n : ℝ))) / (n : ℝ)) := by
  -- The αRTS-FE design is an abstract hitting-time design, for the forced-exploration predicate.
  have hα' : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα.1, hα.2.le⟩
  have hthrottle := fun k ↦ throttle_of_isARTSFE h hARTSFE k
  have hgs := aRTSFE_smallness_all (P := P) (A := A) (Y := Y) θ₀ T hTnn hh
  filter_upwards [consistency_of_hitting h hA θ₀ T hT hTnn hTsum α hα'
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs,
    theta_consistent_of_hitting h hA θ₀ T hT hTnn hTsum α hα'
      (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs hTpos,
    theta_rate_of_hitting h hA hT hTnn hTsum hα' (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs
      hTpos k,
    rho_rate_of_hitting h hA hT hTnn hTsum hα' (aRTSFEUnder A Y θ₀ T hsched) hthrottle hgs
      hTpos hT_diff k] with ω hjω hθω hθrate hrate
  -- The limit `u` of the proportions is the limit `T Θ` of the plug-in targets.
  obtain ⟨u, hu⟩ := hjω
  have hrho : Tendsto (fun n ↦ aRTSTarget A Y θ₀ T n ω k) atTop (𝓝 (T ν.means k)) :=
    tendsto_pi_nhds.mp ((hT.tendsto _).comp hθω) k
  have huk : u k = T ν.means k := tendsto_nhds_unique (hu k).2 hrho
  exact ⟨huk ▸ (hu k).1, tendsto_pi_nhds.mp hθω k, hθrate, hrate⟩

end AlphaRAR.Revised
