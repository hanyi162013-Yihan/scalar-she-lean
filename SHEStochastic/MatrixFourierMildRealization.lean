module

public import SHEStochastic.MatrixMildFourierInput
public import SHEStochastic.MatrixRandomMildExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFourierMildRealization
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
variable (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode)) (u₀ : Physical (d := d))

/-- Concrete integrating-factor equations with arbitrary initial state. -/
def RandomEquation (Z : Ω → Physical (d := d)) : Prop := ∀ (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t ≤ H),
      (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate i a n (U (t,ω))) =ᵐ[μ]
        fun ω => coordinate i a n (Z ω)+
          (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
            (StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)) ω

/-- Deterministic initial-data specialization. -/
def Equation : Prop := RandomEquation F μ H G hG hβ hβ1 U hU N (fun _ => u₀)

/-- A bounded matrix mild solution supplies all original Fourier
integrating-factor equations under one common square-diffusion Brownian
family. Each input is constructed from the solution itself. -/
theorem exists_random_family (Z : Ω → Physical (d := d)) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEq : MatrixRandomMildExistence.Equation G hH N U hU Z) :
    ∃ B : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode),
      RandomEquation F μ H G hG hβ hβ1 U hU B Z := by
  obtain ⟨B,hB⟩ := MatrixAnalyticSquareObservation.exists_family F μ H hH (NativeMatrixEquation.cap G)
    (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.data F G U hU) (NativeMatrixEquation.profile_measurable F G U hU)
    (NativeMatrixEquation.coefficient_measurable F G U hU) N hnull
  refine ⟨B,fun i a n t ht => ?_⟩
  let J := FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis
  let r := StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)
  let c := Real.exp (-(t : ℝ)*(n : ℝ)^2)
  have he := (innerSL ℝ (test i a n)).coeFn_compLpL
    (MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G)
      (NativeMatrixEquation.cap_nonneg G) (MatrixContinuousMild.field G U hU).value
      (MatrixContinuousMild.field G U hU).upper (MatrixContinuousMild.field G U hU).measurable N t ht)
  dsimp only [MatrixContinuousMild.field] at he
  rw [hB t ht (test i a n)] at he
  change J.integral (MatrixMildFourierInput.squareInput F μ H G U hU i a n hH t ht) =ᵐ[μ] _ at he
  rw [MatrixMildFourierInput.input_eq F μ H G hG hβ hβ1 U hU i a n hH t ht,map_smul] at he
  have hs := Lp.coeFn_smul c (J.integral r)
  have hc : Real.exp ((t : ℝ)*(n : ℝ)^2)*c=1 := by
    unfold c
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  filter_upwards [hEq t ht,he,hs] with ω hu ho hs
  rw [hu,map_add]
  rw [MatrixFourierCoordinates.coordinate_heat i a n (t := (t : ℝ)) t.property (Z ω)]
  rw [hs,Pi.smul_apply] at ho
  change c*J.integral r ω=inner ℝ (test i a n) _ at ho
  rw [test_pairing] at ho
  dsimp only [MatrixContinuousMild.field]
  rw [← ho]
  change Real.exp ((t : ℝ)*(n : ℝ)^2)*(c*coordinate i a n (Z ω)+c*J.integral r ω)=_
  rw [mul_add,← mul_assoc,← mul_assoc,hc,one_mul,one_mul]


theorem exists_family (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hEq : MatrixContinuousMild.Equation G hH N U hU u₀) :
    ∃ B : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode),
      Equation F μ H G hG hβ hβ1 U hU B u₀ := by
  exact exists_random_family F μ H G hG hβ hβ1 U hU hH N (fun _ => u₀) hnull hEq

end SHEStochastic.MatrixFourierMildRealization
