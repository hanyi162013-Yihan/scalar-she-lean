module

public import SHEStochastic.NativeMartingaleRecognition
public import SHEStochastic.NativeBrownianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.NativeCharacteristicRecognition
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

/-- Native recognition needs only adapted representatives at each
time, so the limiting canonical filtration need not be completed just
to choose a continuous integral version. All stochastic conclusions
are obtained from the existing integral and compensator proofs. -/
theorem process (r : Process (E := C) F μ H) (M : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M F μ) (hM2 : ∀ t, t ≤ H → MemLp (M t) 2 μ)
    (hCoordinates : ∀ i t, P.W i t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t (RotatedCylindricalCoordinates.constant F μ H (e i))))
    (hzero : M 0 =ᵐ[μ] fun _ ↦ (0 : ℝ))
    (hSquare : Martingale (fun t sample ↦ M t sample^2-PredictableBracket.energy r t sample) F μ)
    (hCross : ∀ i, Martingale (fun t sample ↦ M t sample*P.W i t sample-
      NativeCrossCompensator.value r (RotatedCylindricalCoordinates.constant F μ H (e i)) t sample) F μ) :
    ∀ t, t ≤ H → M t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t r) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hz (t : ℝ≥0) := StoppedItoInputs.stopped_integral_adapted F μ H J t r
  choose N haN hrN using hz
  have hRep (t : ℝ≥0) : N t =ᵐ[μ] J.integral (StoppedItoInputs.stop F μ H t r) := (hrN t).symm
  have hN : Martingale N F μ := ConditionalBracket.martingale J (FiniteCylindricalIto.pastLocality P e) r haN hRep
  have hN2 (t : ℝ≥0) (_ : t ≤ H) : MemLp (N t) 2 μ :=
    (memLp_congr_ae (hRep t)).mpr (Lp.memLp (J.integral (StoppedItoInputs.stop F μ H t r)))
  have hCrossN (i : ι) : Martingale (fun t sample ↦ N t sample*P.W i t sample-
      NativeCrossCompensator.value r (RotatedCylindricalCoordinates.constant F μ H (e i)) t sample) F μ :=
    NativeCrossCompensator.martingale J (FiniteCylindricalIto.pastLocality P e)
      r (RotatedCylindricalCoordinates.constant F μ H (e i)) N (P.W i) haN
      (fun t ↦ (P.adapted i t).stronglyMeasurable) hRep (hCoordinates i)
  exact NativeMartingaleRecognition.process P e r M N hM hN hM2 hN2
    (fun i ↦ NativeCrossCompensator.value r (RotatedCylindricalCoordinates.constant F μ H (e i)))
    hCross hCrossN (fun t _ ↦ hRep t) hzero hSquare

end SHEStochastic.NativeCharacteristicRecognition
