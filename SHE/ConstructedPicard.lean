module

public import SHE.NonlinearConvolution
public import SHE.HeatInitialProcess

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ConstructedPicard
open MeasureTheory Set PredictableL2 LowBands NonlinearHaarIntegrand NonlinearConvolution
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)

/-- Actual forced predictable L² mild fixed point, for the constructed
common-Haar stochastic convolution. The only stochastic input is ordinary
terminal Hilbert Itô integration; a convolution map is not a premise.
This statement is an L²-process theorem, before continuous versions. -/
theorem exists_unique_forced {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hh : (h:ℝ) ≤ 1)
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (forcing : Process (E := StateL2) 𝓕 μ h) :
    ∃! v : Process (E := StateL2) 𝓕 μ h,
      v=forcing+NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I v := by
  exact CompanionPicard.exists_unique_fixedPoint 𝓕 μ h ha hell hb (absBound hell hb) hLip hh hsmall
    (by norm_num : (0:ℝ) ≤ 0) (NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I)
    (undamped_isometry 𝓕 μ h ha hell hb hβ hH hholder hh I) forcing

/-- In particular arbitrary deterministic real spatial L² initial data
produce a unique short-time predictable L² heat mild solution. -/
theorem exists_unique_heat_mild {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hh : (h:ℝ) ≤ 1)
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u₀ : StateL2) :
    ∃! v : Process (E := StateL2) 𝓕 μ h,
      v=HeatInitialProcess.process 𝓕 μ h u₀+
        NonlinearConvolution.map 𝓕 μ h ha hell hb hβ hH hholder I v :=
  exists_unique_forced 𝓕 μ h ha hell hb hβ hH hholder hLip hh hsmall I
    (HeatInitialProcess.process 𝓕 μ h u₀)

/-- A positive horizon is obtained from the proved heat constant, before
choosing any forcing process or initial condition. -/
theorem exists_horizon {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ))) :
    ∃ r : ℝ≥0,0 < r ∧ (r:ℝ) ≤ 1 ∧
      ∀ (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ r)
        (forcing : Process (E := StateL2) 𝓕 μ r),
      ∃! v : Process (E := StateL2) 𝓕 μ r,
        v=forcing+NonlinearConvolution.map 𝓕 μ r ha hell hb hβ hH hholder I v := by
  obtain ⟨r,hr,hr1,hrsmall⟩ := CompanionPicard.exists_contraction_horizon
    (CompanionHeat.picardConstant_nonneg (hell.le.trans ((hb 0).1.trans (hb 0).2)) L)
  exact ⟨r,hr,hr1,fun I forcing =>
    exists_unique_forced 𝓕 μ r ha hell hb hβ hH hholder hLip hr1 hrsmall I forcing⟩

end SHE.ConstructedPicard
