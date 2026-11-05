module

public import SHEStochastic.MatrixEqualCovarianceRotation
public import SHEStochastic.MatrixFourierMildRealization
public import SHEStochastic.NativeMatrixSquareRealization
public import SHEStochastic.MatrixMildCovarianceCongruence
public import SHEStochastic.MatrixFourierNoiseRows
public import SHEStochastic.MatrixFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixFourierCovarianceCongruence
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (G K : MatrixNonlinearCoefficient.Coefficient d) (hCov : ∀ z,G.covariance z=K.covariance z)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)


open MatrixEqualCovarianceRotation
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

/-- The predictable rotation commutes with stopping before every
actual native time, on arbitrary finite horizons. -/
theorem stop_commutes (t : ℝ≥0) (v : Process (E := Input (d := d)) F μ H) :
    PredictableItoRotation.processIsometry F μ H (rotation F G K hCov U hU)
      (MatrixEqualCovarianceRotation.measurable F G K hCov U hU) (StoppedItoInputs.stop F μ H t v)=
    StoppedItoInputs.stop F μ H t (PredictableItoRotation.processIsometry F μ H (rotation F G K hCov U hU)
      (MatrixEqualCovarianceRotation.measurable F G K hCov U hU) v) := by
  apply NativeInputPairing.process_ext
  let R := PredictableItoRotation.processIsometry F μ H (rotation F G K hCov U hU)
    (MatrixEqualCovarianceRotation.measurable F G K hCov U hU)
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H (rotation F G K hCov U hU)
      (MatrixEqualCovarianceRotation.measurable F G K hCov U hU) (StoppedItoInputs.stop F μ H t v),
    StoppedItoInputs.stop_ae F μ H t v,StoppedItoInputs.stop_ae F μ H t (R v),
    PredictableItoRotation.processIsometry_ae F μ H (rotation F G K hCov U hU)
      (MatrixEqualCovarianceRotation.measurable F G K hCov U hU) v] with p hr hv hs hR
  rw [hr,hv,hs]
  by_cases hp : p∈StoppedItoInputs.before (Ω := Ω) t
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,hR]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,map_zero]

variable {C β D γ : ℝ≥0} (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β≤1)
    (hK : HolderWith D γ K.value) (hγ : 0<γ) (hγ1 : γ≤1)

/-- The exact native Fourier input, not only its quadratic covariance,
is carried to the reference input by the one predictable unitary. -/
theorem input_eq (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    PredictableItoRotation.processIsometry F μ H (rotation F G K hCov U hU)
      (MatrixEqualCovarianceRotation.measurable F G K hCov U hU)
      (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)=
    MatrixFourierInput.input F μ H K hK hγ hγ1 U hU i a n := by
  apply NativeInputPairing.process_ext
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H (rotation F G K hCov U hU)
      (MatrixEqualCovarianceRotation.measurable F G K hCov U hU)
      (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n),
    MatrixFourierInput.input_ae F μ H G hG hβ hβ1 U hU i a n,
    MatrixFourierInput.input_ae F μ H K hK hγ hγ1 U hU i a n] with p hr hg hk
  rw [hr,hg,hk]
  exact MatrixEqualCovarianceRotation.row F G K hCov U hU hG hβ hβ1 hK hγ hγ1 H i a n p

include hCov in
/-- A reference Fourier solution admits the literal original diffusion
on every finite horizon, with no restriction H≤1. The state process,
initial variable, probability space and filtration stay the same. -/
theorem exists_family (N : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (Z : Ω → Physical (d := d))
    (hEq : MatrixFourierMildRealization.RandomEquation F μ H K hK hγ hγ1 U hU N Z) :
    ∃ B : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode),
      MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU B Z := by
  obtain ⟨B,hB⟩ := NativePredictableRotation.exists_family N MatrixPredictableHaarRotation.basis
    MatrixPredictableHaarRotation.basis (rotation F G K hCov U hU)
    (MatrixEqualCovarianceRotation.measurable F G K hCov U hU) hnull
  refine ⟨B,?_⟩
  intro i a n t ht
  have he := hB (StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n))
  rw [stop_commutes F G K hCov U hU μ H t _,input_eq F G K hCov U hU μ H hG hβ hβ1 hK hγ hγ1 i a n] at he
  have hs := hEq i a n t ht
  rw [←he] at hs
  exact hs

end SHEStochastic.MatrixFourierCovarianceCongruence
