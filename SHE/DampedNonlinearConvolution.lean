module

public import SHE.DampedStochasticConvolution
public import SHE.NonlinearConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.DampedNonlinearConvolution
open MeasureTheory Set PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
variable {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)

/-- The actual damped state-to-convolution map, including arbitrary
nonnegative damping, built entirely by predictable finite-cell limits. -/
def map (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (u : Process (E := StateL2) 𝓕 μ h) : Process (E := StateL2) 𝓕 μ h :=
  DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell
    (hell.le.trans ((hb 0).1.trans (hb 0).2)) I
    (NonlinearConvolution.field 𝓕 μ h ha hell hb u)
    (NonlinearConvolution.field_predictable 𝓕 μ h ha hell hb hβ hH hholder u)

theorem isometry (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h) :
    CompanionPicard.DampedConvolutionIsometry 𝓕 μ h a ha M (absBound hell hb) Λ
      (map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I) := by
  intro u v
  rw [map,map,DampedStochasticConvolution.difference_causal_isometry]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
  have hst' : s < t := lt_of_le_of_ne hs.2 hst
  have hτ : 0 < (t:ℝ)-(s:ℝ) := sub_pos.mpr (by exact_mod_cast hst')
  apply lintegral_congr
  intro ω
  change ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
    ‖kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),u (s,ω))-
      kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),v (s,ω))‖^2)=_
  rw [kernel_difference_norm_sq ha hell hb hτ]

theorem exists_unique_forced {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
    (hsmall : 2*CompanionHeat.picardConstant ell M L*(h:ℝ)^(1/2:ℝ) ≤ 1/4)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) 𝓕 μ h)
    (forcing : Process (E := StateL2) 𝓕 μ h) :
    ∃! v : Process (E := StateL2) 𝓕 μ h,
      v=forcing+map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I v := by
  exact CompanionPicard.exists_unique_fixedPoint 𝓕 μ h ha hell hb (absBound hell hb) hLip hh hsmall hΛ
    (map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I)
    (isometry 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I) forcing

end SHE.DampedNonlinearConvolution
