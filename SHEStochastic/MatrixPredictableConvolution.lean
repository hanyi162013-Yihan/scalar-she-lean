module

public import SHEStochastic.MatrixHeatKernelModel
public import SHEStochastic.NativeMatrixConvolution
public import SHEStochastic.MatrixNemytskii

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPredictableConvolution
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩

variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))

/-- The full predictable process, constructed from the actual native
infinite Brownian family by the reused finite-cell closure. -/
def convolution (a : Fields (d := d) F U) : Process (E := Physical (d := d)) F μ H :=
  KernelItoLimit.convolution (model F μ H hH U hU) (NativeMatrixConvolution.terminalIto N) a

theorem approximation_tendsto (a : Fields (d := d) F U) :
    Filter.Tendsto (KernelItoLimit.output (model F μ H hH U hU)
      (NativeMatrixConvolution.terminalIto N) a) Filter.atTop
      (nhds (convolution hH U hU N a)) :=
  KernelItoLimit.approximation_tendsto _ _ a

theorem difference_isometry (a b : Fields (d := d) F U) :
    ENNReal.ofReal (‖convolution hH U hU N a-convolution hH U hU N b‖^2) =
      ∫⁻ p, ENNReal.ofReal (‖MatrixHeatKernelModel.raw a p-MatrixHeatKernelModel.raw b p‖^2)
        ∂HaarKernelL2Approximation.measure μ H :=
  KernelItoLimit.difference_isometry _ _ a b

/-- Composition with a predictable vector L2 state uses the already
constructed joint measurable spatial representative. -/
def nonlinearField (G : MatrixNonlinearCoefficient.Coefficient d)
    (u : Process (E := Physical (d := d)) F μ H) : Fields (d := d) F ((G.bound : ℝ)^2+1) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact ⟨MatrixNemytskii.profile G (fun p => u p) (Lp.stronglyMeasurable u),
    fun _ => le_rfl, MatrixNemytskii.covariance_measurable G _ (Lp.stronglyMeasurable u)⟩

/-- The actual nonlinear matrix Haar stochastic convolution. Every
bounded measurable elliptic coefficient defines this predictable map;
smoothness is needed only for the subsequent fixed point estimates. -/
def map (G : MatrixNonlinearCoefficient.Coefficient d)
    (u : Process (E := Physical (d := d)) F μ H) : Process (E := Physical (d := d)) F μ H :=
  convolution hH ((G.bound : ℝ)^2+1) (by positivity) N (nonlinearField G u)

theorem map_difference_isometry (G : MatrixNonlinearCoefficient.Coefficient d)
    (u v : Process (E := Physical (d := d)) F μ H) :
    ENNReal.ofReal (‖map hH N G u-map hH N G v‖^2) =
      ∫⁻ p, ENNReal.ofReal (‖MatrixHeatKernelModel.raw (nonlinearField G u) p-
        MatrixHeatKernelModel.raw (nonlinearField G v) p‖^2)
        ∂HaarKernelL2Approximation.measure μ H :=
  difference_isometry hH _ _ N _ _

end SHEStochastic.MatrixPredictableConvolution
