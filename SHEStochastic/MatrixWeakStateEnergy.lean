module

public import SHEStochastic.MatrixAnalyticEnergy
public import SHEStochastic.MatrixFourierMildRecognition
public import SHE.ProfileVolterra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixWeakStateEnergy
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩

/-- A bounded matrix weak solution started from z has an L2 moment
bound uniform in the initial state and in the chosen weak solution. -/
theorem bound {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : ℝ≥0} (G : MatrixNonlinearCoefficient.Coefficient d)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (hH : (H : ℝ)≤1) (N : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
    (Z : Ω → Physical (d := d)) (z : Physical (d := d)) (hZ : Z =ᵐ[μ] fun _ => z)
    (hEq : MatrixFourierMildRecognition.Equation F μ H G U hU hH N Z)
    (t : ℝ≥0) (ht : t≤H) :
    (∫ ω,‖U (t,ω)‖^2 ∂μ)≤‖z‖^2+
      MatrixAnalyticKernel.constant d (NativeMatrixEquation.cap G)*(2*(t : ℝ)^(1/2 : ℝ)) := by
  let Y := MatrixFourierMildRecognition.convolution F μ H G U hU hH N t ht
  have hc : (∫ ω,Y ω ∂μ)=0 := by
    exact (MatrixSquareAnalyticConvolution.terminalIto F μ H
      (NativeMatrixEquation.profile F G U hU) (NativeMatrixEquation.data F G U hU)
      (NativeMatrixEquation.profile_measurable F G U hU)
      (NativeMatrixEquation.coefficient_measurable F G U hU) N).centered _
  have he : (fun ω => ‖U (t,ω)‖^2) =ᵐ[μ] fun ω => ‖VectorAnalyticHeat.heat t z+Y ω‖^2 := by
    filter_upwards [hEq t ht,hZ] with ω hu hz
    rw [hu,hz]
  rw [integral_congr_ae he,ProfileVolterra.centered_reference_energy μ (Lp.memLp Y) hc,
    ←realLp_norm_sq Y]
  have hb := MatrixAnalyticEnergy.bound hH (NativeMatrixEquation.cap_nonneg G)
    (NativeMatrixEquation.profile F G U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.profile_measurable F G U hU)
    (MatrixSquareAnalyticConvolution.terminalIto F μ H
      (NativeMatrixEquation.profile F G U hU) (NativeMatrixEquation.data F G U hU)
      (NativeMatrixEquation.profile_measurable F G U hU)
      (NativeMatrixEquation.coefficient_measurable F G U hU) N) t ht
  have hR : 0≤MatrixAnalyticKernel.constant d (NativeMatrixEquation.cap G)*(2*(t : ℝ)^(1/2 : ℝ)) :=
    mul_nonneg (MatrixAnalyticKernel.constant_nonneg (NativeMatrixEquation.cap_nonneg G)) (by positivity)
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (VectorAnalyticHeat.contraction _ _) 2)
    ((ENNReal.ofReal_le_ofReal_iff hR).mp hb)

end SHEStochastic.MatrixWeakStateEnergy
