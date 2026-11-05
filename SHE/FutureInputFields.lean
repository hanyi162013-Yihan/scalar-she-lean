module

public import SHE.FutureResidualScoreInput
public import SHE.VariableScoreInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledResidualScoreInput
open Set MeasureTheory AddCircle StoppedFourier StoppedGaussianFeatures
local instance futureInputFields_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {W : Type*} [MeasurableSpace W] {n : ℕ}

/-- The literal future score input is jointly Borel in all original
relative locations and the translated output root, without fixed rank
or invertibility hypotheses. -/
theorem futureInput_variable_centers_measurable (σ target : Fin n→ℝ)
    (center : W→Fin n→HeatCircle) (hcenter : Measurable center)
    (c e : Domain→ℝ) (hc : Measurable c) (he : Measurable e) (q : ℝ) :
    Measurable (fun p : W×HeatCircle=>futureInput σ target (center p.1) c e q p.2) := by
  have hc' : Measurable (fun p=>c (StoppedTimeTranslation.shift q p)) :=
    hc.comp (StoppedTimeTranslation.shift q).measurable
  have he' : Measurable (fun p=>e (StoppedTimeTranslation.shift q p)) :=
    he.comp (StoppedTimeTranslation.shift q).measurable
  have hh := StoppedScoreLeverage.scoreInput_variable_centers_measurable
    (fun i=>σ i-q) (fun i=>target i-q) center hcenter
    (fun p=>c (StoppedTimeTranslation.shift q p)) (fun p=>e (StoppedTimeTranslation.shift q p)) hc' he'
  convert! hh using 1
  funext p
  exact congrFun (StoppedTimeTranslation.score_input_shift σ target (center p.1) c e q) p.2

end SHE.ControlledResidualScoreInput
