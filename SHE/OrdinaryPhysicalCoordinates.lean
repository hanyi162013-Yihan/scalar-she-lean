module
public import SHE.OrdinaryUncutPhysicalColumns

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
namespace SHE.OrdinaryPhysicalCoordinates
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel CutoffWordHistories GaussianConvolution
open scoped NNReal ENNReal
local instance ordinaryPhysicalCoordinates_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryPhysicalCoordinates_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryPhysicalCoordinates_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryPhysicalCoordinates_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryPhysicalCoordinates_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)(k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "Obs"=>(NL).observations.observations
local notation "Term"=>(NL).terminal

/-- The full ordinary-U derivative coordinate, zero outside its genuine
current window. The original uncut word normalization occurs once. -/
def coordinate(ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:History Y k×(ℝ≥0×Ω)):ℝ:=
  if R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<Term z.1 then
    fderiv ℝ (gaussianAverage (covariance R.reference (Obs z.1) (z.2.1:ℝ) (Term z.1))
      (UncutSmoothWords.test L k z.1)) (OrdinaryPhysicalGradient.mean m NL z)
        (WithLp.toLp 2 (fun i:Fin (n+k)=>ℓ (OrdinaryPhysicalGradient.row m (Obs z.1) z.2 i)))
  else 0

theorem coordinate_eq(ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:History Y k×(ℝ≥0×Ω)):
    ℓ (OrdinaryUncutPhysicalGradient.raw m L k z)=coordinate m L k ℓ z:=by
  by_cases hq:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<Term z.1
  · rw [coordinate,if_pos hq]
    exact OrdinaryUncutPhysicalColumns.action m L k ℓ z hq
  · simp only [coordinate,if_neg hq,OrdinaryUncutPhysicalGradient.raw,
      OrdinaryPhysicalGradient.raw,if_neg hq,smul_zero,map_zero]

end SHE.OrdinaryPhysicalCoordinates
