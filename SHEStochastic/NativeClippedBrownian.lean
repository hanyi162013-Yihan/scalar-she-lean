module

public import SHEStochastic.NativeHorizonCharacteristics
public import SHEStochastic.FiniteCylindricalLocality
public import SHEStochastic.CanonicalBrownianSubGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.NativeClippedBrownian
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2
open scoped NNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (K : ℝ≥0) (hK : K ≤ H) (i : ι)

def value (q : ℝ≥0) (ω : Ω) : ℝ := P.W i (min q K) ω-P.W i 0 ω

include hK e in
theorem martingale : Martingale (value P K i) F μ := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let v := RotatedCylindricalCoordinates.constant F μ H (e i)
  have ha : StronglyAdapted F (fun q ↦ P.W i (min q K)) := fun q ↦
    ((P.adapted i (min q K)).mono (F.mono (min_le_left _ _)) le_rfl).stronglyMeasurable
  have hr (q : ℝ≥0) : P.W i (min q K) =ᵐ[μ] J.integral
      (StoppedItoInputs.stop F μ H q (StoppedItoInputs.stop F μ H K v)) := by
    rw [StoppedInputAlgebra.stop_stop, ← NNReal.coe_min]
    exact (FiniteCylindricalIto.coordinate_integral P e i (min q K) ((min_le_right _ _).trans hK)).symm
  have hm := ConditionalBracket.martingale J (FiniteCylindricalIto.pastLocality P e)
    (StoppedItoInputs.stop F μ H K v) ha hr
  apply hm.congr
  · intro q
    exact (ha q).sub (((P.adapted i 0).mono (F.mono (show (0 : ℝ≥0) ≤ q from zero_le)) le_rfl).stronglyMeasurable)
  · intro q
    filter_upwards [FiniteScalarIto.zero_ae P.toCoordinates i] with ω hω
    simp only [value, hω, sub_zero]

include hK in
theorem subgaussian (q : ℝ≥0) : HasSubgaussianMGF (value P K i q) (min q K) μ := by
  have hs := CanonicalBrownianSubGaussian.of_law μ (min q K)
    (BrownianCoordinates.eval_law F μ H P.W P.law i (min q K) ((min_le_right _ _).trans hK))
  apply hs.congr
  filter_upwards [FiniteScalarIto.zero_ae P.toCoordinates i] with ω hω
  simp only [value, hω, sub_zero]

end SHEStochastic.NativeClippedBrownian
