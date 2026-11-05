module

public import SHEStochastic.JointPathState
public import SHEStochastic.NativeContinuationDriverInput
public import SHEStochastic.PastedHeatProductIntegrability
public import SHEStochastic.NativeCharacteristicRecognition
public import SHEStochastic.BoundedFourierMildRecognition

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.JointPathNativeFourier
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

def mode (a : ℂ →L[ℝ] ℝ) (n : ℤ) (q : ℝ≥0) (x : JointPathFiltration.Space (E := RealL2) (ι := ι) H) : ℝ :=
  value H (row a n) ((n : ℝ)^2) x (AdaptedCanonicalPathTests.clock H q)

def input (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F ν H :=
  BoundedFourierInput.input F ν H U hU hG hβ hβ1 B hb a n

theorem mode_eq (a : ℂ →L[ℝ] ℝ) (n : ℤ) (q : ℝ≥0)
    (x : JointPathFiltration.Space (E := RealL2) (ι := ι) H) :
    mode H a n q x = Real.exp ((min q H : ℝ≥0)*(n : ℝ)^2)*NativeFourierHeatCoordinate.coordinate a n (U q x)-
      NativeFourierHeatCoordinate.coordinate a n (U 0 x) := by
  rw [JointPathState.initial]
  change Real.exp ((n : ℝ)^2*(AdaptedCanonicalPathTests.clock H q).val)*
    NativeFourierHeatCoordinate.coordinate a n (x (AdaptedCanonicalPathTests.clock H q)).1-
      NativeFourierHeatCoordinate.coordinate a n (x (origin H)).1 = _
  simp only [JointPathState.state, AdaptedCanonicalPathTests.clock, NNReal.coe_min, mul_comm]

variable (P : FiniteScalarIto.Family (JointPathFiltration.filtration (E := RealL2) (ι := ι) H) ν H ι)
variable (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
variable (hP : ∀ i q, P.W i q = JointPathFiltration.driver (E := RealL2) (ι := ι) H i q)

include e in
theorem energy (a : ℂ →L[ℝ] ℝ) (n : ℤ) (q : ℝ≥0) :
    PredictableBracket.energy (input H ν hG hβ hβ1 B hb a n) q =ᵐ[ν]
      fun x ↦ PastedHeatCovariance.value H ((n : ℝ)^2+(n : ℝ)^2) (by positivity)
        (NativeContinuationProductInput.diagonal (ι := ι) hG hβ hβ1 B hb a n) x
        (AdaptedCanonicalPathTests.clock H q) := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := e.repr.toHomeomorph.secondCountableTopology
  filter_upwards [NativeFourierCompensatorValue.energy_ae hG hβ hβ1 B hb a n F ν H U hU,
    NativeHorizonCharacteristics.energy_clip (input H ν hG hβ hβ1 B hb a n) q] with x he hc
  rw [← hc]
  unfold input
  rw [he (min q H) (min_le_right _ _), NativeContinuationProductInput.diagonal, JointPathState.covariance]
  apply intervalIntegral.integral_congr
  intro s _
  congr 1
  congr 1
  ring

theorem mixed (a : ℂ →L[ℝ] ℝ) (n : ℤ) (i : ι) (q : ℝ≥0) :
    NativeCrossCompensator.value (input H ν hG hβ hβ1 B hb a n)
      (RotatedCylindricalCoordinates.constant F ν H (e i)) q =ᵐ[ν]
      fun x ↦ PastedHeatCovariance.value H ((n : ℝ)^2+0) (by positivity)
        (NativeContinuationProductInput.mixed hG hβ hβ1 B hb e a n i) x (AdaptedCanonicalPathTests.clock H q) := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := e.repr.toHomeomorph.secondCountableTopology
  filter_upwards [NativeFourierCompensatorValue.mixed_ae hG hβ hβ1 B hb a n F ν H U hU (e i),
    NativeHorizonCharacteristics.cross_clip (input H ν hG hβ hβ1 B hb a n)
      (RotatedCylindricalCoordinates.constant F ν H (e i)) q] with x he hc
  rw [← hc]
  unfold input
  rw [he (min q H) (min_le_right _ _), NativeContinuationProductInput.mixed, JointPathState.covariance]
  apply intervalIntegral.integral_congr
  intro s _
  congr 1
  congr 1
  ring

include hP in
theorem driver_value (i : ι) (q : ℝ≥0) (x : JointPathFiltration.Space (E := RealL2) (ι := ι) H) :
    value H (NativeUniformFourierMixed.driverRow i) 0 x (AdaptedCanonicalPathTests.clock H q) = P.W i q x := by
  rw [hP]
  change Real.exp (0*(AdaptedCanonicalPathTests.clock H q).val)*(x (AdaptedCanonicalPathTests.clock H q)).2 i-
    (x (origin H)).2 i = _
  simp only [zero_mul, Real.exp_zero, one_mul, JointPathFiltration.driver]

include P e hP in
theorem driver_envelope_memLp (i : ι) : MemLp (envelope H (NativeUniformFourierMixed.driverRow i) 0) 4 ν := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := e.repr.toHomeomorph.secondCountableTopology
  apply NativeDriverPathMoments.envelope_memLp F ν H P e H le_rfl id i _ measurable_id
  intro t x
  change value H (NativeUniformFourierMixed.driverRow i) 0 x t =
    P.W i (AdaptedCanonicalPathTests.toNN H t) x-P.W i 0 x
  have hh := driver_value H ν P hP i (AdaptedCanonicalPathTests.toNN H t) x
  rw [AdaptedCanonicalPathTests.clock_toNN] at hh
  rw [hh, show P.W i 0 x = 0 from by rw [hP, JointPathFiltration.driver_zero], sub_zero]

include P hP in
/-- Product identities in the full joint path filtration identify the
SAME native Fourier integral, without moving to another sample space. -/
theorem process (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (hMode : PastedLinearHeatMartingale.Identity H (row (ι := ι) a n) ((n : ℝ)^2) ν)
    (hSquare : PastedHeatProductMartingale.Identity H (row (ι := ι) a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
      (by positivity) (NativeContinuationProductInput.diagonal (ι := ι) hG hβ hβ1 B hb a n) ν)
    (hMixed : ∀ i, PastedHeatProductMartingale.Identity H (row a n) (NativeUniformFourierMixed.driverRow i) ((n : ℝ)^2) 0
      (by positivity) (NativeContinuationProductInput.mixed hG hβ hβ1 B hb e a n i) ν)
    (hEnv : MemLp (envelope H (row (ι := ι) a n) ((n : ℝ)^2)) 4 ν) :
    ∀ t, t ≤ H → mode H a n t =ᵐ[ν] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F ν H t (input H ν hG hβ hβ1 B hb a n)) := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := e.repr.toHomeomorph.secondCountableTopology
  have hm4 (q : ℝ≥0) : MemLp (mode (ι := ι) H a n q) 4 ν :=
    PastedHeatProductIntegrability.linear_memLp H (row a n) ((n : ℝ)^2) ν id measurable_id _ measurable_const _ hEnv
      (Filter.Eventually.of_forall fun x ↦ value_bound H (row a n) ((n : ℝ)^2) x _)
  have hM := PastedLinearHeatMartingale.martingale H (row a n) ((n : ℝ)^2) ν F
    (JointPathFiltration.evaluation_adapted H) (fun _ ↦ le_rfl) hMode (hEnv.mono_exponent (by norm_num))
  have hd4 (i : ι) (q : ℝ≥0) : MemLp (fun x ↦ value H (NativeUniformFourierMixed.driverRow i) 0 x
      (AdaptedCanonicalPathTests.clock H q)) 4 ν :=
    PastedHeatProductIntegrability.linear_memLp H (NativeUniformFourierMixed.driverRow i) 0 ν id measurable_id _ measurable_const _
      (driver_envelope_memLp H ν P e hP i) (Filter.Eventually.of_forall fun x ↦ value_bound H _ _ x _)
  have hS := PastedHeatProductMartingale.martingale H (row a n) (row a n) ((n : ℝ)^2) ((n : ℝ)^2)
    (by positivity) (NativeContinuationProductInput.diagonal hG hβ hβ1 B hb a n) ν F
    (JointPathFiltration.evaluation_adapted H) (fun _ ↦ le_rfl) hSquare (fun q ↦
      (QuadraticMomentBounds.product_memLp ν (hm4 q) (hm4 q)).sub
        (PastedHeatProductIntegrability.covariance_memLp H _ _ _ ν id measurable_id _ measurable_const))
  have hC (i : ι) := PastedHeatProductMartingale.martingale H (row a n) (NativeUniformFourierMixed.driverRow i) ((n : ℝ)^2) 0
    (by positivity) (NativeContinuationProductInput.mixed hG hβ hβ1 B hb e a n i) ν F
    (JointPathFiltration.evaluation_adapted H) (fun _ ↦ le_rfl) (hMixed i) (fun q ↦
      (QuadraticMomentBounds.product_memLp ν (hm4 q) (hd4 i q)).sub
        (PastedHeatProductIntegrability.covariance_memLp H _ _ _ ν id measurable_id _ measurable_const))
  have hSquareNative : Martingale (fun q x ↦ mode (ι := ι) H a n q x^2-
      PredictableBracket.energy (input H ν hG hβ hβ1 B hb a n) q x) F ν := by
    apply hS.congr
    · intro q
      exact ((hM.stronglyAdapted q).pow 2).sub (PredictableBracket.measurable _ q).stronglyMeasurable
    · intro q
      filter_upwards [energy H ν hG hβ hβ1 B hb e a n q] with x hx
      simp only [PastedHeatProductFunctional.value, mode, pow_two, hx]
  have hMixedNative (i : ι) : Martingale (fun q x ↦ mode H a n q x*P.W i q x-
      NativeCrossCompensator.value (input H ν hG hβ hβ1 B hb a n)
        (RotatedCylindricalCoordinates.constant F ν H (e i)) q x) F ν := by
    apply (hC i).congr
    · intro q
      let r := input H ν hG hβ hβ1 B hb a n
      let v := RotatedCylindricalCoordinates.constant F ν H (e i)
      exact ((hM.stronglyAdapted q).mul (P.adapted i q).stronglyMeasurable).sub
        ((((PredictableBracket.measurable r q).stronglyMeasurable.add
          (PredictableBracket.measurable v q).stronglyMeasurable).sub
            (PredictableBracket.measurable (r-v) q).stronglyMeasurable).div stronglyMeasurable_const)
    · intro q
      filter_upwards [mixed H ν hG hβ hβ1 B hb e a n i q] with x hx
      simp only [PastedHeatProductFunctional.value, driver_value H ν P hP, mode, hx]
  have hclip (i : ι) (q : ℝ≥0) : P.W i q = P.W i (min q H) := by
    rw [hP, hP]
    funext x
    simp only [JointPathFiltration.driver, AdaptedCanonicalPathTests.clock, NNReal.coe_min, min_assoc, min_self]
  apply NativeCharacteristicRecognition.process P e (input H ν hG hβ hβ1 B hb a n) _ hM
    (fun q _ ↦ (hm4 q).mono_exponent (by norm_num)) (NativeHorizonCharacteristics.coordinates P e hclip)
    _ hSquareNative hMixedNative
  exact Filter.Eventually.of_forall fun x ↦ by
    have hz : AdaptedCanonicalPathTests.clock H 0 = origin H := Subtype.ext (min_eq_left H.property)
    simp only [mode, hz, value_origin]


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
    BoundedFourierMildRecognition.HasClosedVersion F ν H U hU hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) (U 0) := by
  apply BoundedFourierMildRecognition.exists_closed F ν H U hU hG hβ hβ1 B hb P e (U 0) hH
    (JointPathState.continuous H)
  intro T hTH hT a n
  have hh := process H ν hG hβ hβ1 B hb P e hP a n (hMode a n) (hSquare a n) (hMixed a n) (hEnv a n) T hTH
  have he : mode (ι := ι) H a n T = fun sample ↦ Real.exp ((T : ℝ)*(n : ℝ)^2)*
      NativeFourierHeatCoordinate.coordinate a n (U T sample)-NativeFourierHeatCoordinate.coordinate a n (U 0 sample) := by
    funext x
    rw [mode_eq, min_eq_left hTH]
  simpa only [he, input] using hh

end SHEStochastic.JointPathNativeFourier
