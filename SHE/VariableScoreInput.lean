module

public import SHE.StoppedScoreL2
public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.StoppedScoreLeverage
open Set MeasureTheory AddCircle StoppedFourier StoppedGaussianFeatures
  MeasurableGaussianScores
local instance variableScoreInput_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {n : ℕ} {W : Type*} [MeasurableSpace W]

/-- Joint measurability in all relative observation locations and the
output translation; singular covariance ranks are included. -/
theorem scoreInput_variable_centers_measurable
    (σ target : Fin n→ℝ) (center : W→Fin n→HeatCircle) (hcenter : Measurable center)
    (c e : Domain→ℝ) (hc : Measurable c) (he : Measurable e) :
    Measurable (fun p : W×HeatCircle=>scoreInput σ target (center p.1) c e p.2) := by
  let Z : VariableObservations.Family (W×HeatCircle) n :=
    { observations := fun p i=>⟨σ i,target i,center p.1 i+p.2⟩
      stop_measurable := fun _=>measurable_const
      target_measurable := fun _=>measurable_const
      center_measurable := fun i=>
        (((measurable_pi_apply i).comp hcenter).comp measurable_fst).add measurable_snd }
  have hA := StoppedGaussianFields.covariance_measurable Z (hc.comp measurable_snd)
    (measurable_const : Measurable (fun _ : W×HeatCircle=>(0:ℝ)))
  have hD := StoppedGaussianFields.row_measurable Z
  have hS : Measurable (fun p : (W×HeatCircle)×Domain=>
      scoreVariance (StoppedGaussianFields.covariance Z (fun z=>c z.2) (fun _=>0) p.1)
        (StoppedGaussianFields.row Z p.1 p.2)) := by
    exact (scoreVariance_measurable (n:=n)).comp ((hA.comp measurable_fst).prodMk hD)
  convert! ((((continuous_abs.measurable.comp he).comp measurable_snd).mul hS).stronglyMeasurable.integral_prod_right').measurable using 1
  infer_instance

end SHE.StoppedScoreLeverage
