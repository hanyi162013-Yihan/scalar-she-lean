module

public import SHE.TimeDilationPathPull

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
variable (c : ℝ≥0) (hc : 0<c) (h : ℝ≥0)

/-- State paths return without a Brownian Jacobian. This compensating
normalization is the inverse of the unnormalized predictable state pull. -/
def pushStateProcess (u : Process (E:=E) 𝓕 μ h) :
    Process (E:=E) (filtration 𝓕 (clock c hc)) μ (c*h):=
  Real.sqrt (c:ℝ) • (processEquivalence 𝓕 μ c hc h).symm u

theorem pushStateProcess_ae (u : Process (E:=E) 𝓕 μ h)
    (U : ℝ≥0→Ω→E) (hU : u=ᵐ[energyMeasure μ h] Function.uncurry U) :
    pushStateProcess 𝓕 μ c hc h u=ᵐ[energyMeasure μ (c*h)]
      (fun p=>U ((clock c hc).symm p.1) p.2) := by
  have hrev:=ScaledLpPull.inverse_preserving (energyMeasure μ h) (energyMeasure μ (c*h))
    (c:ℝ) hc (ambientEquiv c hc) (energyMeasure_clock_preserving c hc h μ)
  have he:=hrev.quasiMeasurePreserving.ae hU
  have he':=(Measure.ae_ennreal_smul_measure_iff
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (show (0:ℝ)<c from hc)))).mp he
  have hs:=ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.sqrt (c:ℝ))
    ((processEquivalence 𝓕 μ c hc h).symm u))
  filter_upwards [hs,processEquivalence_symm_ae 𝓕 μ c hc h u,he'] with p hp hu hvalue
  change u ((clock c hc).symm p.1,p.2)=U ((clock c hc).symm p.1) p.2 at hvalue
  unfold pushStateProcess
  rw [hp]
  change Real.sqrt (c:ℝ) • (processEquivalence 𝓕 μ c hc h).symm u p=_
  rw [hu,hvalue,smul_smul,ScaledLpPull.sqrt_mul_sqrt_inv (c:ℝ) hc,one_smul]

end SHE.PredictableTimeDilation
