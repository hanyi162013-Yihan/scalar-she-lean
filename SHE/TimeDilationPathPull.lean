module

public import SHE.TimeDilationInverseIto
public import SHE.ClockedPairFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set Filter PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

/-- Pulling a physical path to the faster clock does not multiply its
state by a Brownian Jacobian. Only integrands acquire that factor. -/
def pullPath (U : ℝ≥0→Ω→E) (t : ℝ≥0) : Ω→E:=U (clock c hc t)

omit [MeasurableSpace Ω] [InnerProductSpace ℝ E] in
theorem pullPath_continuous (U : ℝ≥0→Ω→E)
    (hU : ∀ ω,Continuous (fun t=>U t ω)) (ω : Ω) :
    Continuous (fun t=>pullPath c hc U t ω):=(hU ω).comp (clock_continuous c hc)

omit [InnerProductSpace ℝ E] in
theorem pullPath_predictable (U : ℝ≥0→Ω→E)
    (hU : StronglyMeasurable[(filtration 𝓕 (clock c hc)).predictable] (Function.uncurry U)) :
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (pullPath c hc U)):=
  hU.comp_measurable (measurable_forward 𝓕 (clock c hc))

/-- The unnormalized state pull is a bounded map on predictable L².
Its explicit normalization compensates the integrand isometry. -/
def pullStateProcess (u : Process (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h)) :
    Process (E:=E) 𝓕 μ h:=
  (Real.sqrt (c:ℝ))⁻¹ • processIsometry 𝓕 μ c hc h u

theorem pullStateProcess_ae (u : Process (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h))
    (U : ℝ≥0→Ω→E) (hU : u=ᵐ[energyMeasure μ (c*h)] Function.uncurry U) :
    pullStateProcess 𝓕 μ c hc h u=ᵐ[energyMeasure μ h] Function.uncurry (pullPath c hc U) := by
  have he:=(energyMeasure_clock_preserving c hc h μ).quasiMeasurePreserving.ae hU
  have he':=(Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hc)).mp he
  have hs:=ae_eq_of_ae_eq_trim (Lp.coeFn_smul ((Real.sqrt (c:ℝ))⁻¹)
    (processIsometry 𝓕 μ c hc h u))
  filter_upwards [hs,processIsometry_ae 𝓕 μ c hc h u,he'] with p hp hu hvalue
  change pullStateProcess 𝓕 μ c hc h u p=U (clock c hc p.1) p.2
  unfold pullStateProcess
  rw [hp]
  change (Real.sqrt (c:ℝ))⁻¹ • processIsometry 𝓕 μ c hc h u p=_
  rw [hu,hvalue]
  simp only [Function.uncurry_apply_pair,smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (show (0:ℝ)<c from hc)).ne',one_smul]

omit [MeasurableSpace Ω] in
/-- No path version or exceptional set is changed by the clock
round trip: the two state paths agree pointwise. -/
theorem path_pullPath (U : ℝ≥0→Ω→LowBands.StateL2) :
    ClockedPairFields.path c hc (pullPath c hc U)=U := by
  funext t ω
  simp only [ClockedPairFields.path,pullPath,OrderIso.apply_symm_apply]

/-- Any original filtration is the physical-clock image of its literal
inverse-clock filtration. -/
theorem filtration_inverse_clock (𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    filtration (filtration 𝓖 (clock c hc).symm) (clock c hc)=𝓖 := by
  apply Filtration.ext
  funext t
  change 𝓖 (clock c hc ((clock c hc).symm t))=𝓖 t
  rw [OrderIso.apply_symm_apply]

end SHE.PredictableTimeDilation
