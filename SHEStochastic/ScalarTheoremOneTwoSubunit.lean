module

public import SHEStochastic.ScalarPhysicalDriftedLaw
public import SHEStochastic.ScalarDriftedBoundedNative
public import SHEStochastic.ScalarDriftedStrictNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarTheoremOneTwoSubunit
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarStatePathFiltration UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "r" => NativeClock.rate
local notation "e" => ScalarUnboundedFourierProjection.basis
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

private theorem same_row {Ω : Type} [MeasurableSpace Ω] (W : ℝ≥0→Ω→RealL2)
    {g : ℝ→ℝ} {C D β γ : ℝ≥0} (hg : HolderWith C β g) (hg' : HolderWith D γ g)
    (hβ : 0<β) (hβ₁ : β≤1) (hγ : 0<γ) (hγ₁ : γ≤1)
    (N : ℕ) (t : ℝ≥0) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ScalarPhysicalStoppedEquation.row hg hβ hβ₁ W N t ψ n =
      ScalarPhysicalStoppedEquation.row hg' hγ hγ₁ W N t ψ n := by
  unfold ScalarPhysicalStoppedEquation.row
  congr 1

/-- Actual continuous scalar mild state law, independent of the choice
of the Hölder estimate used to build each stopped input. -/
def Realizes (H : ℝ≥0) (g : ℝ→ℝ) (b : ScalarLinearGrowthDriftField.Data H)
    (u₀ : RealL2) (law : Measure (Space H)) : Prop :=
  ∃ (C β : ℝ≥0) (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1),
    ScalarPhysicalDriftedLaw.Realizes H hg hβ hβ₁ b u₀ e law

theorem realizes_iff (H : ℝ≥0) {g : ℝ→ℝ} {C β : ℝ≥0}
    (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) (law : Measure (Space H)) :
    Realizes H g b u₀ law ↔ ScalarPhysicalDriftedLaw.Realizes H hg hβ hβ₁ b u₀ e law := by
  constructor
  · rintro ⟨D,γ,hg',hγ,hγ₁,Ω,m,S,hLaw⟩
    let _ : MeasurableSpace Ω := m
    have hEq : ScalarPhysicalStoppedEquation.Equation S.F S.μ H hg hβ hβ₁ b u₀ S.W
        (FiniteCylindricalIto.terminalIto S.P.toCoordinates e) := by
      intro N t ht ψ n
      obtain ⟨v,hv,he⟩ := S.equation N t ht ψ n
      rw [same_row S.W hg' hg hγ hγ₁ hβ hβ₁ N t ψ n] at hv
      exact ⟨v,hv,he⟩
    exact ⟨Ω,m,⟨S.μ,S.F,S.W,S.predictable,S.continuous,S.nulls,S.P,S.initial,hEq⟩,hLaw⟩
  · exact fun h => ⟨C,β,hg,hβ,hβ₁,h⟩

private def nativeLower (c : ℝ≥0) : ℝ≥0 :=
  ⟨ScalarUnitTorusFourierClock.scale*(c : ℝ),
    mul_nonneg ScalarUnitTorusFourierClock.scale_pos.le c.property⟩

private theorem nativeLower_pos {c : ℝ≥0} (hc : 0<c) : 0<nativeLower c :=
  mul_pos ScalarUnitTorusFourierClock.scale_pos (show (0 : ℝ)<c from hc)

private theorem nativeLower_bound {g : ℝ→ℝ} {c : ℝ≥0} (hell : ∀ z,(c : ℝ)≤|g z|) :
    ∀ z,(nativeLower c : ℝ)≤|ScalarUnitTorusFourierClock.nativeCoefficient g z| :=
  ScalarUnitTorusFourierClock.elliptic hell

/-- Manuscript Theorem 1.2(i), including every positive Hölder
exponent, on the original unit torus with its physical clock. -/
theorem theorem_1_2_i (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β)
    (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B) (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) :
    ∃! law,Realizes H g b u₀ law := by
  obtain ⟨D,γ,hγ,hγ₁,hg'⟩ := ScalarBoundedWellPosed.effective_exponent hg hβ B hb
  have hN := ScalarDriftedBoundedNative.exists_unique (r*H) (mul_pos NativeClock.rate_pos hH)
    (ScalarUnitTorusFourierClock.holder hg') hγ hγ₁ (ScalarPhysicalDriftClock.native b) u₀
    (nativeLower c) (nativeLower_pos hc) (nativeLower_bound hell)
    (ScalarUnitTorusFourierClock.nativeBound B) (ScalarUnitTorusFourierClock.bounded hb) e
  have hP := ScalarPhysicalDriftedLaw.exists_unique H hg' hγ hγ₁.le b u₀ e hN
  simpa only [realizes_iff H hg' hγ hγ₁.le b u₀] using hP

/-- The strict subunit part of manuscript Theorem 1.2(ii), with
bounded initial data and no upper bound on the diffusion. -/
theorem theorem_1_2_ii_of_lt_one (H : ℝ≥0) (hH : 0<H)
    {g : ℝ→ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
    (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)
    (hInf : MemLp (u₀ : AddCircle (1 : ℝ) → ℝ) ⊤ haarAddCircle) :
    ∃! law,Realizes H g b u₀ law := by
  have hfinite : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u₀≠⊤ := ne_of_lt hInf
  have hR := ENNReal.ofReal_toReal hfinite
  have hN := ScalarDriftedStrictNative.exists_unique (r*H) (mul_pos NativeClock.rate_pos hH)
    (ScalarUnitTorusFourierClock.holder hg) hβ hβ₁ (ScalarPhysicalDriftClock.native b) u₀
    (nativeLower c) (nativeLower_pos hc) (nativeLower_bound hell) _ ENNReal.toReal_nonneg hR.symm
  have hP := ScalarPhysicalDriftedLaw.exists_unique H hg hβ hβ₁.le b u₀ e hN
  simpa only [realizes_iff H hg hβ hβ₁.le b u₀] using hP

end SHEStochastic.ScalarTheoremOneTwoSubunit
