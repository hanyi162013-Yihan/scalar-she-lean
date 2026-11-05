module

public import SHEStochastic.JointPathState
public import SHEStochastic.NativeContinuationDriverInput
public import SHEStochastic.PastedHeatProductIntegrability
public import SHEStochastic.NativeCharacteristicRecognition
public import SHEStochastic.GlobalBoundedFourierRecognition
public import SHEStochastic.JointPathNativeFourier

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalJointPathNativeFourier
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩


variable {V ι : Type*} [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (H : ℝ≥0) (ν : Measure (JointPathFiltration.Space (E := RealL2) (ι := ι) H)) [IsProbabilityMeasure ν]
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩
local notation "F" => JointPathFiltration.filtration (E := RealL2) (ι := ι) H
local notation "U" => JointPathState.state (E := RealL2) (ι := ι) H
local notation "hU" => JointPathState.predictable (E := RealL2) (ι := ι) H

open JointPathNativeFourier

variable (P : FiniteScalarIto.Family (JointPathFiltration.filtration (E := RealL2) (ι := ι) H) ν H ι)
variable (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
variable (hP : ∀ i q, P.W i q = JointPathFiltration.driver (E := RealL2) (ι := ι) H i q)

include P hP in
/-- The recognized native Fourier equations give the actual bounded
mild equation on the same joint path space and with the same driver. -/
theorem exists_closed (hH : 0 < H)
    (hMode : ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ), PastedLinearHeatMartingale.Identity H (row (ι := ι) a n) ((n : ℝ)^2) ν)
    (hSquare : ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ), PastedHeatProductMartingale.Identity H (row (ι := ι) a n) (row a n)
      ((n : ℝ)^2) ((n : ℝ)^2) (by positivity) (NativeContinuationProductInput.diagonal (ι := ι) hG hβ hβ1 B hb a n) ν)
    (hMixed : ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ) i, PastedHeatProductMartingale.Identity H (row a n)
      (NativeUniformFourierMixed.driverRow i) ((n : ℝ)^2) 0 (by positivity)
      (NativeContinuationProductInput.mixed hG hβ hβ1 B hb e a n i) ν)
    (hEnv : ∀ (a : ℂ →L[ℝ] ℝ) (n : ℤ), MemLp (envelope H (row (ι := ι) a n) ((n : ℝ)^2)) 4 ν) :
    GlobalBoundedFourierRecognition.HasClosedVersion F ν H U hU hG hβ hβ1 B hb hH
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) (U 0) := by
  apply GlobalBoundedFourierRecognition.exists_closed F ν H U hU hG hβ hβ1 B hb P e (U 0) hH
    (JointPathState.continuous H)
  intro T hTH a n
  have hh := process H ν hG hβ hβ1 B hb P e hP a n (hMode a n) (hSquare a n) (hMixed a n) (hEnv a n) T hTH
  have he : mode (ι := ι) H a n T = fun sample ↦ Real.exp ((T : ℝ)*(n : ℝ)^2)*
      NativeFourierHeatCoordinate.coordinate a n (U T sample)-NativeFourierHeatCoordinate.coordinate a n (U 0 sample) := by
    funext x
    rw [mode_eq, min_eq_left hTH]
  simpa only [he, input] using hh

end SHEStochastic.GlobalJointPathNativeFourier
