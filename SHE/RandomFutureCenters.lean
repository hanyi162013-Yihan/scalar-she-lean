module

public import SHE.RandomFutureInputFields
public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set MeasureTheory AddCircle StoppedFourier StoppedGaussianFeatures MeasurableGaussianScores
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {W : Type*} [MeasurableSpace W] {n : ℕ}

/-- True joint Borel score mass for jointly varying centers, residual coefficients and
signed profile inputs, including varying singular Gaussian covariances. -/
theorem futureInput_random_centers_measurable (σ target : Fin n→ℝ) (center : W→Fin n→HeatCircle) (hcenter : Measurable center)
    (c e : W×Domain→ℝ) (hc : Measurable c) (he : Measurable e) (q : ℝ) :
    Measurable (fun p : W×HeatCircle=>futureInput σ target (center p.1)
      (fun z=>c (p.1,z)) (fun z=>e (p.1,z)) q p.2) := by
  let Z : VariableObservations.Family (W×HeatCircle) n :=
    { observations := fun p i=>⟨σ i,target i,center p.1 i+p.2⟩
      stop_measurable := fun _=>measurable_const
      target_measurable := fun _=>measurable_const
      center_measurable := fun i=>(((measurable_pi_apply i).comp hcenter).comp measurable_fst).add measurable_snd }
  have hA := StoppedGaussianFields.covariance_measurable Z
    (hc.comp (measurable_fst.fst.prodMk measurable_snd))
    (measurable_const : Measurable (fun _ : W×HeatCircle=>q))
  have hR := StoppedGaussianFields.row_measurable Z
  have hS : Measurable (fun p : (W×HeatCircle)×Domain=>
      scoreVariance (StoppedGaussianFields.covariance Z (fun z=>c (z.1.1,z.2))
        (fun _=>q) p.1) (StoppedGaussianFields.row Z p.1 p.2)) :=
    scoreVariance_measurable.comp ((hA.comp measurable_fst).prodMk hR)
  have he' : Measurable (fun p : (W×HeatCircle)×Domain=>|e (p.1.1,p.2)|) :=
    continuous_abs.measurable.comp (he.comp (measurable_fst.fst.prodMk measurable_snd))
  convert! ((he'.mul hS).stronglyMeasurable.integral_prod_right'
    (ν:=StoppedGaussianFeatures.historyMeasure q)).measurable using 1

end SHE.ControlledResidualScoreInput
