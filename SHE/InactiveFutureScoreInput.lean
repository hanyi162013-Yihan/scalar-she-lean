module

public import SHE.StoppedInactiveCoordinate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.InactiveFutureScoreInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement GaussianCoordinates MeasurableGaussianScores ControlledResidualScoreInput
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {n : ℕ}

/-- The true newest sigma=q future score input is exactly its original
older-frame input, including the singular covariance and any signed
coefficient source. The zero coordinate has no conditioning cost. -/
theorem future_input_eq (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hages : ∀ i,σ i≤target i) (q T : ℝ) (hT : q≤T) (x0 : HeatCircle)
    (c : Domain→ℝ) (hc : Measurable c) {ell U : ℝ} (hell : 0<ell)
    (hb : ∀ p,ell≤c p ∧ c p≤U) (e : Domain→ℝ) (x : HeatCircle) :
    futureInput (Fin.cons q σ) (Fin.cons T target) (Fin.cons x0 center) c e q x=
      futureInput σ target center c e q x := by
  have hcent : (fun i : Fin (n+1)=>(Fin.cons x0 center : Fin (n+1)→HeatCircle) i+x)=
      (Fin.cons (x0+x) (fun i=>center i+x) : Fin (n+1)→HeatCircle) := by
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  unfold futureInput
  rw [hcent]
  apply integral_congr_ae
  filter_upwards [StoppedInactiveCoordinate.score_ae σ target (fun i=>center i+x) hages q T hT
    (x0+x) c hc hell hb] with p hp
  rw [hp]

end SHE.InactiveFutureScoreInput
