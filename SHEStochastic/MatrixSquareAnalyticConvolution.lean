module

public import SHEStochastic.MatrixAnalyticSquareObservation

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixSquareAnalyticConvolution
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

/-- The original square-diffusion integral, expressed through the
proved predictable unitary on the existing analytic Haar kernel. This
construction does not require completing the canonical filtration. -/
def scalarIto (N : FiniteScalarIto.Family F μ H (d×HaarNode)) :
    StandardTerminalIto (C := Input (d := d)) (E := ℝ) F μ H :=
  PredictableItoRotation.integral F μ H (NativeMatrixCoefficient.isometry Q A)
    (NativeMatrixCoefficient.measurable F Q A hQ hA)
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)

def terminalIto (N : FiniteScalarIto.Family F μ H (d×HaarNode)) :
    StandardTerminalIto (C := MatrixHaarKernel.Columns (d := d)) (E := Physical (d := d)) F μ H :=
  HilbertTerminalIto.terminalIto F μ H VectorWhiteCoordinates.basis (scalarIto F μ H Q A hQ hA N)

def value (N : FiniteScalarIto.Family F μ H (d×HaarNode)) (t : ℝ≥0) (ht : t ≤ H) :
    Lp (Physical (d := d)) 2 μ :=
  (terminalIto F μ H Q A hQ hA N).integral
    (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)

/-- Every spatial observation of the constructed Hilbert convolution
is the native integral of its literal G* heat* row. -/
theorem commutes (N : FiniteScalarIto.Family F μ H (d×HaarNode))
    (t : ℝ≥0) (ht : t ≤ H) (v : Physical (d := d)) :
    (innerSL ℝ v).compLpL 2 μ (value F μ H hH cap hcap Q hUpper A hQ hA N t ht)=
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (MatrixAnalyticSquareObservation.input F μ H hH cap hcap Q hUpper A hQ hA t ht v) :=
  HilbertTerminalIto.commutes F μ H VectorWhiteCoordinates.basis (scalarIto F μ H Q A hQ hA N)
    (innerSL ℝ v) (MatrixAnalyticConvolution.input F μ H hH cap hcap Q hUpper hQ t ht)

end SHEStochastic.MatrixSquareAnalyticConvolution
