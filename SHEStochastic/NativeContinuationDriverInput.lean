module

public import SHEStochastic.NativeContinuationProductInput
public import SHEStochastic.NativeDriverPathMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.NativeContinuationDriverInput
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open StoppedPathPasting PastedLinearHeatFunctional NativeContinuationFourierInput
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {ι : Type*} [Countable ι] [DecidableEq ι]



variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (H : ℝ≥0) (Q : Measure (CanonicalFourierFluctuation.Space (ι := ι) H)) [IsProbabilityMeasure Q]
  (e : HilbertBasis ι ℝ C)
  (hBrown : ∀ d (a : Fin d → ι), FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration H) Q H
    (fun i ↦ CanonicalStateDriverFiltration.coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0))

include hBrown in
theorem restart_read (v : ι → ℝ) (i : ι) (t : Time H) (x : CanonicalFourierFluctuation.Space (ι := ι) H) :
    value H (NativeUniformFourierMixed.driverRow i) 0 (JointStateDriverPath.restart H v x) t =
      (CanonicalNativeFourierRecognition.family H Q hBrown).W i (AdaptedCanonicalPathTests.toNN H t) x-
        (CanonicalNativeFourierRecognition.family H Q hBrown).W i 0 x := by
  have hh := NativeContinuationProductInput.driver_restart_value H v i (AdaptedCanonicalPathTests.toNN H t) x
  rw [AdaptedCanonicalPathTests.clock_toNN] at hh
  exact hh

include hBrown e in
theorem restart_martingale (v : ι → ℝ) (i : ι) :
    Martingale (fun q x ↦ value H (NativeUniformFourierMixed.driverRow i) 0 (JointStateDriverPath.restart H v x)
      (AdaptedCanonicalPathTests.clock H q)) (CanonicalStateDriverFiltration.filtration H) Q :=
  NativeDriverPathMoments.martingale (CanonicalStateDriverFiltration.filtration H) Q H
    (CanonicalNativeFourierRecognition.family H Q hBrown) e H le_rfl (JointStateDriverPath.restart H v) i
    (restart_read H Q hBrown v i)

include hBrown e in
theorem restart_fourth (v : ι → ℝ) (i : ι) :
    (∫⁻ y, ENNReal.ofReal ((envelope H (NativeUniformFourierMixed.driverRow i) 0 y)^4)
      ∂Q.map (JointStateDriverPath.restart H v)) ≤ LinearHeatMaximumMoments.fourthConstant H := by
  have hX : Measurable (JointStateDriverPath.restart H v : CanonicalFourierFluctuation.Space (ι := ι) H →
      Path H (JointStateDriverPath.State RealL2 ι)) :=
    (JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map ((continuous_envelope H (NativeUniformFourierMixed.driverRow i) 0).measurable.pow_const 4).ennreal_ofReal hX]
  exact NativeDriverPathMoments.fourth_bound (CanonicalStateDriverFiltration.filtration H) Q H
    (CanonicalNativeFourierRecognition.family H Q hBrown) e H le_rfl (JointStateDriverPath.restart H v) i
    (restart_read H Q hBrown v i)

include hBrown e in
theorem restart_identity (v : ι → ℝ) (i : ι) :
    PastedLinearHeatMartingale.Identity H (NativeUniformFourierMixed.driverRow i) 0
      (Q.map (JointStateDriverPath.restart H v)) := by
  exact PastedLinearHeatMartingale.source_identity H (NativeUniformFourierMixed.driverRow i) 0
    (CanonicalStateDriverFiltration.filtration H) Q (JointStateDriverPath.restart H v)
    ((JointStateDriverPath.measurable_restart H).comp (measurable_const.prodMk measurable_id))
    (NativeContinuationCharacteristics.restart_adapted H v) (restart_martingale H Q e hBrown v i)

include e in
theorem properties (h : NativeContinuationCharacteristics.BrownianInput H Q) :
    ∀ᵐ u ∂CanonicalInitialKernel.initialLaw H Q, ∀ v : ι → ℝ, ∀ i : ι,
      PastedLinearHeatMartingale.Identity H (NativeUniformFourierMixed.driverRow i) 0
        (NativeContinuationKernel.joint H Q (u,v)) ∧
      (∫⁻ y, ENNReal.ofReal ((envelope H (NativeUniformFourierMixed.driverRow i) 0 y)^4)
        ∂NativeContinuationKernel.joint H Q (u,v)) ≤ LinearHeatMaximumMoments.fourthConstant H := by
  filter_upwards [h] with u hu v i
  rw [NativeContinuationKernel.joint, JointStateDriverPath.continuationKernel_apply]
  exact ⟨restart_identity H (CanonicalInitialKernel.kernel H Q u) e hu v i,
    restart_fourth H (CanonicalInitialKernel.kernel H Q u) e hu v i⟩

end SHEStochastic.NativeContinuationDriverInput
