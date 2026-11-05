module

public import SHEStochastic.ScalarTheoremOneTwoSubunit
public import SHEStochastic.ScalarDriftedLipschitzNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarTheoremOneTwo
open MeasureTheory SHE SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "r" => NativeClock.rate
local notation "e" => ScalarUnboundedFourierProjection.basis

abbrev Realizes := ScalarTheoremOneTwoSubunit.Realizes

/-- Theorem 1.2(i), with normalized Haar measure and the physical
unit-torus heat generator. -/
theorem theorem_1_2_i (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B) (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) :
    ∃! law,Realizes H g b u₀ law :=
  ScalarTheoremOneTwoSubunit.theorem_1_2_i H hH hg hβ B hb c hc hell b u₀

/-- The unbounded Lipschitz endpoint of Theorem 1.2(ii). -/
theorem theorem_1_2_ii_lipschitz (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
    (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) :
    ∃! law,Realizes H g b u₀ law := by
  let d : ℝ≥0 := ⟨ScalarUnitTorusFourierClock.scale*(c : ℝ),
    mul_nonneg ScalarUnitTorusFourierClock.scale_pos.le c.property⟩
  have hd : 0<d := mul_pos ScalarUnitTorusFourierClock.scale_pos (show (0 : ℝ)<c from hc)
  have hdg : ∀ z,(d : ℝ)≤|ScalarUnitTorusFourierClock.nativeCoefficient g z| :=
    ScalarUnitTorusFourierClock.elliptic hell
  have hN := ScalarDriftedLipschitzNative.exists_unique (r*H) (mul_pos NativeClock.rate_pos hH)
    (ScalarUnitTorusFourierClock.holder hg) (ScalarPhysicalDriftClock.native b) u₀ e d hd hdg
  have hP := ScalarPhysicalDriftedLaw.exists_unique H hg zero_lt_one le_rfl b u₀ e hN
  simpa only [Realizes,ScalarTheoremOneTwoSubunit.realizes_iff H hg zero_lt_one le_rfl b u₀] using hP

/-- Theorem 1.2(ii), for the entire stated range (0<β≤1) and
bounded deterministic initial data. No upper bound on the diffusion
coefficient is assumed. -/
theorem theorem_1_2_ii (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
    (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
    (hInf : MemLp (u₀ : AddCircle (1 : ℝ) → ℝ) ⊤ haarAddCircle) :
    ∃! law,Realizes H g b u₀ law := by
  rcases lt_or_eq_of_le hβ₁ with hβ' | rfl
  · exact ScalarTheoremOneTwoSubunit.theorem_1_2_ii_of_lt_one H hH hg hβ hβ' c hc hell b u₀ hInf
  · exact theorem_1_2_ii_lipschitz H hH hg c hc hell b u₀

end SHEStochastic.ScalarTheoremOneTwo
