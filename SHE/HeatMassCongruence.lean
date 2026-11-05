module

public import SHE.HeatFieldWeightedLimit

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace SHE.HeatMassCongruence
open MeasureTheory StoppedFourier NativeHeatObservation HeatFieldWeightedLimit
open DyadicApproximation
local instance heatMassCongruence_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P : Type*} [MeasurableSpace P]

theorem state (U V : P→RealL2) (A : ℝ→ℝ) (D : P×HeatCircle→ℝ) (ε : ℝ) (p : P) (h : U p=V p) :
    mass U A D ε p=mass V A D ε p := by
  unfold mass difference PredictableScalarField.nativeField PredictableScalarField.unitField
  simp only [Prod.fst,Prod.snd]
  rw [h]

theorem weight (U : P→RealL2) (A : ℝ→ℝ) (D E : P×HeatCircle→ℝ) (ε : ℝ) (p : P)
    (h : ∀ x,D (p,x)=E (p,x)) : mass U A D ε p=mass U A E ε p := by
  unfold mass
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [h x])

end SHE.HeatMassCongruence
