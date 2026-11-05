module

public import SHEStochastic.MatrixFiniteHorizonKernel
public import SHEStochastic.MatrixSquareAnalyticConvolution
public import SHEStochastic.NativeMatrixSquareRealization

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixFiniteHorizonSquareConvolution
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
    (H : ℝ≥0) (cap : ℝ) (hcap : 0  ≤  cap)
    (Q : ℝ≥0×Ω → Profile d) (hUpper : ∀ p,(Q p).upper  ≤  cap)
    (A : ∀ p,Data (Q p))
    (hQ : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
    (hA : @Measurable ((ℝ≥0×Ω)×AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (A z.1).value z.2))
local notation "ν" => (energyMeasure μ H).trim (predictable_le_product F)

def haarInput (t : ℝ≥0) (ht : t  ≤  H) (v : Physical (d := d)) : Process (E := Input (d := d)) F μ H :=
  (HilbertColumns.mapCLM (innerSL ℝ v)).compLpL 2 ν
    (MatrixFiniteHorizonKernel.input F μ H cap hcap Q hUpper hQ t ht)

def input (t : ℝ≥0) (ht : t  ≤  H) (v : Physical (d := d)) : Process (E := Input (d := d)) F μ H :=
  PredictableItoRotation.processIsometry F μ H (NativeMatrixCoefficient.isometry Q A)
    (NativeMatrixCoefficient.measurable F Q A hQ hA) (haarInput F μ H cap hcap Q hUpper hQ t ht v)

/-- Analytic-clock square-diffusion inputs are the literal causal
G(U)* heat* rows in the fixed white coordinates. -/
theorem input_ae (t : ℝ≥0) (ht : t  ≤  H) (v : Physical (d := d)) :
    input F μ H cap hcap Q hUpper A hQ hA t ht v =ᵐ[energyMeasure μ H]
      fun p => if (p.1 : ℝ)<(t : ℝ) then
        (A p).factor.adjoint ((VectorAnalyticHeat.heat ((t : ℝ)-(p.1 : ℝ))).adjoint v) else 0 := by
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H
    (NativeMatrixCoefficient.isometry Q A) (NativeMatrixCoefficient.measurable F Q A hQ hA)
      (haarInput F μ H cap hcap Q hUpper hQ t ht v),
    ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM (innerSL ℝ v)).coeFn_compLpL
      (MatrixFiniteHorizonKernel.input F μ H cap hcap Q hUpper hQ t ht)),
    MatrixFiniteHorizonKernel.input_ae F μ H cap hcap Q hUpper hQ t ht] with p hi ho hk
  change PredictableItoRotation.processIsometry F μ H _ _ _ p=_ at hi
  dsimp only [input]
  rw [hi]
  change haarInput F μ H cap hcap Q hUpper hQ t ht v p=_ at ho
  rw [ho,hk,MatrixAnalyticKernel.kernel,MatrixCausalHeatRows.mapped_kernel,MatrixCausalHeatRows.row]
  by_cases hp : (p.1 : ℝ)<(t : ℝ)
  · rw [if_pos hp,if_pos (div_pos (sub_pos.mpr hp) NativeHeatObservation.timeScale_pos)]
    exact (A p).reconstruct_adjoint _
  · rw [if_neg hp,if_neg (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (not_lt.mp hp)) NativeHeatObservation.timeScale_pos.le)),map_zero]

/-- The actual original-square Hilbert stochastic convolution is
constructed on any finite terminal horizon. -/
def value (N : FiniteScalarIto.Family F μ H (d×HaarNode)) (t : ℝ≥0) (ht : t ≤ H) :
    Lp (Physical (d := d)) 2 μ :=
  (MatrixSquareAnalyticConvolution.terminalIto F μ H Q A hQ hA N).integral
    (MatrixFiniteHorizonKernel.input F μ H cap hcap Q hUpper hQ t ht)

theorem commutes (N : FiniteScalarIto.Family F μ H (d×HaarNode))
    (t : ℝ≥0) (ht : t ≤ H) (v : Physical (d := d)) :
    (innerSL ℝ v).compLpL 2 μ (value F μ H cap hcap Q hUpper A hQ hA N t ht)=
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (input F μ H cap hcap Q hUpper A hQ hA t ht v) :=
  HilbertTerminalIto.commutes F μ H VectorWhiteCoordinates.basis (MatrixSquareAnalyticConvolution.scalarIto F μ H Q A hQ hA N)
    (innerSL ℝ v) (MatrixFiniteHorizonKernel.input F μ H cap hcap Q hUpper hQ t ht)

theorem centered (N : FiniteScalarIto.Family F μ H (d×HaarNode)) (t : ℝ≥0) (ht : t ≤ H) :
    (∫ ω,value F μ H cap hcap Q hUpper A hQ hA N t ht ω ∂μ)=0 :=
  (MatrixSquareAnalyticConvolution.terminalIto F μ H Q A hQ hA N).centered _

end SHEStochastic.MatrixFiniteHorizonSquareConvolution
