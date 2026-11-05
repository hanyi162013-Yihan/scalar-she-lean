module

public import SHEStochastic.MatrixAnalyticObservation
public import SHEStochastic.NativeMatrixSquareRealization

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixAnalyticSquareObservation
open MeasureTheory SHE SHE.FiniteHaar SHE.PredictableL2 MatrixInfiniteHaar MatrixSquareCoefficient
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (cap : ℝ) (hcap : 0 ≤ cap)
    (Q : ℝ≥0×Ω → Profile d) (hUpper : ∀ p,(Q p).upper ≤ cap)
    (A : ∀ p,Data (Q p))
    (hQ : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
    (hA : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (A z.1).value z.2))
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)

def haarInput (t : ℝ≥0) (ht : t ≤ H) (v : Physical (d := d)) : Process (E := Input (d := d)) F μ H :=
  (HilbertColumns.mapCLM (innerSL ℝ v)).compLpL 2 ν
    (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)

def input (t : ℝ≥0) (ht : t ≤ H) (v : Physical (d := d)) : Process (E := Input (d := d)) F μ H :=
  PredictableItoRotation.processIsometry F μ H (NativeMatrixCoefficient.isometry Q A)
    (NativeMatrixCoefficient.measurable F Q A hQ hA) (haarInput F μ H hH cap hcap Q hUpper hQ t ht v)

/-- Analytic-clock square-diffusion inputs are the literal causal
G(U)* heat* rows in the fixed white coordinates. -/
theorem input_ae (t : ℝ≥0) (ht : t ≤ H) (v : Physical (d := d)) :
    input F μ H hH cap hcap Q hUpper A hQ hA t ht v =ᵐ[energyMeasure μ H]
      fun p => if (p.1 : ℝ)<(t : ℝ) then
        (A p).factor.adjoint ((VectorAnalyticHeat.heat ((t : ℝ)-(p.1 : ℝ))).adjoint v) else 0 := by
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H
    (NativeMatrixCoefficient.isometry Q A) (NativeMatrixCoefficient.measurable F Q A hQ hA)
      (haarInput F μ H hH cap hcap Q hUpper hQ t ht v),
    ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (innerSL ℝ v)).coeFn_compLpL
      (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)),
    MatrixAnalyticConvolution.input_ae F μ H hH cap hcap Q hUpper hQ t ht] with p hi ho hk
  change PredictableItoRotation.processIsometry F μ H _ _ _ p=_ at hi
  dsimp only [input]
  rw [hi]
  change haarInput F μ H hH cap hcap Q hUpper hQ t ht v p=_ at ho
  rw [ho,hk,MatrixAnalyticKernel.kernel,MatrixCausalHeatRows.mapped_kernel,MatrixCausalHeatRows.row]
  by_cases hp : (p.1 : ℝ)<(t : ℝ)
  · rw [if_pos hp,if_pos (div_pos (sub_pos.mpr hp) NativeHeatObservation.timeScale_pos)]
    exact (A p).reconstruct_adjoint _
  · rw [if_neg hp,if_neg (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (not_lt.mp hp)) NativeHeatObservation.timeScale_pos.le)),map_zero]

/-- Reverse rotation applies simultaneously to every analytic-clock
observation, on the original probability space and filtration. -/
theorem exists_family (N : FiniteScalarIto.Family F μ H (d×HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ B : FiniteScalarIto.Family F μ H (d×HaarNode),∀ t ht v,
      (innerSL ℝ v).compLpL 2 μ (MatrixAnalyticConvolution.value F μ H hH cap hcap Q hUpper hQ N t ht)=
        (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (input F μ H hH cap hcap Q hUpper A hQ hA t ht v) := by
  obtain ⟨B,hB⟩ := NativeMatrixSquareRealization.exists_transport F μ H Q A hQ hA N hnull
  refine ⟨B,fun t ht v => ?_⟩
  have he := HilbertTerminalIto.commutes F μ H VectorWhiteCoordinates.basis
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)
    (innerSL ℝ v) (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)
  exact he.trans (hB (haarInput F μ H hH cap hcap Q hUpper hQ t ht v)).symm

/-- The forward predictable rotation realizes an original square-
diffusion equation by the covariance-adapted analytic Haar convolution. -/
theorem exists_haar_family (N : FiniteScalarIto.Family F μ H (d×HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ B : FiniteScalarIto.Family F μ H (d×HaarNode),∀ t ht v,
      (innerSL ℝ v).compLpL 2 μ (MatrixAnalyticConvolution.value F μ H hH cap hcap Q hUpper hQ B t ht)=
        (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
          (input F μ H hH cap hcap Q hUpper A hQ hA t ht v) := by
  obtain ⟨B,hB⟩ := NativePredictableRotation.exists_family N MatrixPredictableHaarRotation.basis
    MatrixPredictableHaarRotation.basis (NativeMatrixCoefficient.isometry Q A)
    (NativeMatrixCoefficient.measurable F Q A hQ hA) hnull
  refine ⟨B,fun t ht v => ?_⟩
  have he := HilbertTerminalIto.commutes F μ H VectorWhiteCoordinates.basis
    (FiniteCylindricalIto.terminalIto B.toCoordinates MatrixPredictableHaarRotation.basis)
    (innerSL ℝ v) (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)
  exact he.trans (hB (haarInput F μ H hH cap hcap Q hUpper hQ t ht v))

end SHEStochastic.MatrixAnalyticSquareObservation
