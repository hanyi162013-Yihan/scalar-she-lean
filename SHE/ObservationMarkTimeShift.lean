module

public import SHE.ObservationTimeShift
public import SHE.FiniteWordScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SHE.ObservationTimeShift
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion GaussianConvolution
  StoppedGaussianFeatures
local instance observationMarkTimeShift_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

/-- Exact translation of the literal signed continuum covariance mark.
The original separate stops, signed profile direction and entire test
are retained, with no integrability or rank premise in this identity. -/
theorem covarianceMark_translation (v q : ℝ) (σ T : Fin n→ℝ) (center : Fin n→HeatCircle)
    (A : Matrix (Fin n) (Fin n) ℝ) (e : Domain→ℝ) (F : State n→ℝ) (m : State n) :
    FiniteWordScores.covarianceMark (historyMeasure (q+v)) A (profile v e)
      (stoppedRow (fun i=>σ i+v) (fun i=>T i+v) center) F m=
      FiniteWordScores.covarianceMark (historyMeasure q) A e (stoppedRow σ T center) F m := by
  unfold FiniteWordScores.covarianceMark
  rw [←integral_history_translation v q]
  apply congrArg (fun z : ℝ=>(1/2:ℝ)*z)
  apply integral_congr_ae
  exact ae_of_all _ (fun p=>by dsimp only; rw [profile_translation,stoppedRow_translation])

end SHE.ObservationTimeShift
