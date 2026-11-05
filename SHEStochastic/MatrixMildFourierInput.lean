module

public import SHEStochastic.MatrixFourierInput
public import SHEStochastic.MatrixFourierNoiseRows
public import SHEStochastic.MatrixAnalyticSquareObservation
public import SHEStochastic.MatrixContinuousMild

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixMildFourierInput
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
variable (hH : (H : ℝ) ≤ 1)

def squareInput (t : ℝ≥0) (ht : t ≤ H) : Process (E := Input (d := d)) F μ H :=
  MatrixAnalyticSquareObservation.input F μ H hH (NativeMatrixEquation.cap G)
    (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.data F G U hU) (NativeMatrixEquation.profile_measurable F G U hU)
    (NativeMatrixEquation.coefficient_measurable F G U hU) t ht (test i a n)

/-- The exact Fourier form of the actual nonlinear analytic-clock input.
A single growing predictable process represents all terminal times. -/
theorem input_eq (t : ℝ≥0) (ht : t ≤ H) :
    squareInput F μ H G U hU i a n hH t ht=
      Real.exp (-(t : ℝ)*(n : ℝ)^2) •
        StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n) := by
  let r := MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n
  have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_smul
    (Real.exp (-(t : ℝ)*(n : ℝ)^2)) (StoppedItoInputs.stop F μ H t r))
  apply NativeInputPairing.process_ext
  filter_upwards [MatrixAnalyticSquareObservation.input_ae F μ H hH (NativeMatrixEquation.cap G)
    (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.data F G U hU) (NativeMatrixEquation.profile_measurable F G U hU)
    (NativeMatrixEquation.coefficient_measurable F G U hU) t ht (test i a n),
    StoppedItoInputs.stop_ae F μ H t r,MatrixFourierInput.input_ae F μ H G hG hβ hβ1 U hU i a n,hs]
    with p hsq hstop hrow hsmul
  change squareInput F μ H G U hU i a n hH t ht p=_ at hsq
  rw [hsq,hsmul,Pi.smul_apply,hstop]
  by_cases hp : (p.1 : ℝ)<(t : ℝ)
  · rw [if_pos hp,Set.indicator_of_mem (show p ∈ StoppedItoInputs.before (Ω := Ω) t from hp)]
    have hr : r p=MatrixFourierInput.row H G hG hβ hβ1 U i a n p := hrow
    rw [hr,MatrixFourierNoiseRows.factor_heat G hG hβ hβ1
      (NativeMatrixEquation.data F G U hU p) (U p)
      (NativeMatrixEquation.coefficient_ae F G U hU p) i a n (sub_pos.mpr hp).le]
    unfold MatrixFourierInput.row FourierHeatInput.multiplier
    rw [← mul_smul,← Real.exp_add]
    congr 2
    rw [min_eq_left (hp.le.trans (by exact_mod_cast ht))]
    ring
  · rw [if_neg hp,Set.indicator_of_notMem (show p ∉ StoppedItoInputs.before (Ω := Ω) t from hp),smul_zero]

end SHEStochastic.MatrixMildFourierInput
