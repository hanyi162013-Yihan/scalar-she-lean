module

public import SHEStochastic.MatrixFourierMildRealization
public import SHEStochastic.MatrixSquareAnalyticConvolution
public import SHEStochastic.MatrixRandomMildExistence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFourierMildRecognition
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
    (N : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))


/-- The constructed original square-diffusion stochastic convolution. -/
def convolution (t : ℝ≥0) (ht : t ≤ H) : Lp (Physical (d := d)) 2 μ :=
  MatrixSquareAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G)
    (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.data F G U hU) (NativeMatrixEquation.profile_measurable F G U hU)
    (NativeMatrixEquation.coefficient_measurable F G U hU) N t ht

def Equation (Z : Ω → Physical (d := d)) : Prop := ∀ t (ht : t ≤ H),
  (fun ω => U (t,ω)) =ᵐ[μ] fun ω => VectorAnalyticHeat.heat t (Z ω)+convolution F μ H G U hU hH N t ht ω

variable (Z : Ω → Physical (d := d))
    (hFourier : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU N Z)

/-- One concrete component Fourier equation; only a countable real and
imaginary family is needed to reconstruct the full mild state. -/
def CoordinateEquation (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Prop :=
  ∀ t : ℝ≥0, t ≤ H →
    (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate i a n (U (t,ω))) =ᵐ[μ]
      fun ω => coordinate i a n (Z ω)+
        (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)) ω

/-- The native Fourier equations give every concrete component
coordinate of the full constructed Hilbert mild equation. -/
theorem coordinate_eq_of (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (hCoordinate : CoordinateEquation F μ H G hG hβ hβ1 U hU N Z i a n) (t : ℝ≥0) (ht : t ≤ H) :
    (fun ω => coordinate i a n (U (t,ω))) =ᵐ[μ]
      fun ω => coordinate i a n (VectorAnalyticHeat.heat t (Z ω)+convolution F μ H G U hU hH N t ht ω) := by
  let J := FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis
  let r := StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)
  let c := Real.exp (-(t : ℝ)*(n : ℝ)^2)
  let v := convolution F μ H G U hU hH N t ht
  have ho := (innerSL ℝ (test i a n)).coeFn_compLpL v
  dsimp only [v,convolution] at ho
  rw [MatrixSquareAnalyticConvolution.commutes] at ho
  change J.integral (MatrixMildFourierInput.squareInput F μ H G U hU i a n hH t ht) =ᵐ[μ] _ at ho
  rw [MatrixMildFourierInput.input_eq F μ H G hG hβ hβ1 U hU i a n hH t ht,map_smul] at ho
  have hs := Lp.coeFn_smul c (J.integral r)
  have hc : c*Real.exp ((t : ℝ)*(n : ℝ)^2)=1 := by
    unfold c
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  filter_upwards [hCoordinate t ht,ho,hs] with ω hf ho hs
  rw [map_add,MatrixFourierCoordinates.coordinate_heat i a n (t := (t : ℝ)) t.property (Z ω)]
  rw [hs,Pi.smul_apply] at ho
  change c*J.integral r ω=inner ℝ (test i a n) (v ω) at ho
  rw [test_pairing] at ho
  change coordinate i a n (U (t,ω))=c*coordinate i a n (Z ω)+coordinate i a n (v ω)
  calc
    _ = c*(Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate i a n (U (t,ω))) := by
      rw [← mul_assoc,hc,one_mul]
    _ = c*(coordinate i a n (Z ω)+J.integral r ω) := congrArg (fun z : ℝ => c*z) hf
    _ = _ := by rw [mul_add,ho]


include hFourier in
theorem coordinate_eq (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t ≤ H) :
    (fun ω => coordinate i a n (U (t,ω))) =ᵐ[μ]
      fun ω => coordinate i a n (VectorAnalyticHeat.heat t (Z ω)+convolution F μ H G U hU hH N t ht ω) := by
  exact coordinate_eq_of F μ H G hG hβ hβ1 U hU hH N Z i a n (hFourier i a n) t ht

/-- Countably many genuine Fourier equations suffice for the entire
vector mild equation, without an uncountable simultaneous-null-set premise. -/
theorem equation_of_basis
    (hBasis : ∀ i n,
      CoordinateEquation F μ H G hG hβ hβ1 U hU N Z i Complex.reCLM n ∧
      CoordinateEquation F μ H G hG hβ hβ1 U hU N Z i Complex.imCLM n) :
    Equation F μ H G U hU hH N Z := by
  intro t ht
  apply MatrixFourierCoordinates.ae_eq μ
    (fun ω => U (t,ω)) (fun ω => VectorAnalyticHeat.heat t (Z ω)+convolution F μ H G U hU hH N t ht ω)
  · intro i n
    exact coordinate_eq_of F μ H G hG hβ hβ1 U hU hH N Z i Complex.reCLM n (hBasis i n).1 t ht
  · intro i n
    exact coordinate_eq_of F μ H G hG hβ hβ1 U hU hH N Z i Complex.imCLM n (hBasis i n).2 t ht


include hFourier in
/-- Countable Fourier separation recovers the original nonlinear
matrix mild equation as an equality of vector-valued L2 states. -/
theorem equation : Equation F μ H G U hU hH N Z := by
  intro t ht
  apply MatrixFourierCoordinates.ae_eq μ
    (fun ω => U (t,ω)) (fun ω => VectorAnalyticHeat.heat t (Z ω)+convolution F μ H G U hU hH N t ht ω)
  · intro i n
    exact coordinate_eq F μ H G hG hβ hβ1 U hU hH N Z hFourier i Complex.reCLM n t ht
  · intro i n
    exact coordinate_eq F μ H G hG hβ hβ1 U hU hH N Z hFourier i Complex.imCLM n t ht

include hFourier in
/-- On a completed filtration the same weak mild solution has a genuine
covariance-adapted Haar realization, without changing its state process. -/
theorem exists_haar_equation (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ B : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode),
      MatrixRandomMildExistence.Equation G hH B U hU Z := by
  obtain ⟨B,hB⟩ := MatrixAnalyticSquareObservation.exists_haar_family F μ H hH (NativeMatrixEquation.cap G)
    (NativeMatrixEquation.cap_nonneg G) (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.data F G U hU) (NativeMatrixEquation.profile_measurable F G U hU)
    (NativeMatrixEquation.coefficient_measurable F G U hU) N hnull
  have hv (t : ℝ≥0) (ht : t ≤ H) : convolution F μ H G U hU hH N t ht=
      MatrixAnalyticConvolution.value F μ H hH (NativeMatrixEquation.cap G) (NativeMatrixEquation.cap_nonneg G)
        (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
        (NativeMatrixEquation.profile_measurable F G U hU) B t ht := by
    apply HilbertLpObservations.ext μ VectorWhiteCoordinates.basis
    intro j
    rw [convolution,MatrixSquareAnalyticConvolution.commutes,hB t ht (VectorWhiteCoordinates.basis j)]
  refine ⟨B,?_⟩
  intro t ht
  have he := equation F μ H G hG hβ hβ1 U hU hH N Z hFourier t ht
  rw [hv t ht] at he
  simpa only [MatrixContinuousMild.field] using he

end SHEStochastic.MatrixFourierMildRecognition
