module
public import SHE.PredictableScalarHaarRotation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.PredictableScalarHaarRotation
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle PredictableL2
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor StoppedFourier
open scoped NNReal ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (D : SmoothApproximation.ScalarData)
variable (U : ℝ≥0 × Ω → RealL2) (hU : StronglyMeasurable[𝓕.predictable] U)

/-- The original observation input has the literal one-noise physical
coefficient g(U), strict causal support and zero auxiliary coordinate. -/
theorem originalRow_ae {T t : ℝ} (ht : t < T) (x : HeatCircle) :
    originalRow 𝓕 μ H D U hU ht x =ᵐ[energyMeasure μ H]
      (fun p => if (p.1:ℝ) < t then
        WithLp.toLp 2
          (ScalarSplittingInputs.originalInput haarAddCircle (ScalarHaarRotation.scalar D (U p))
            (ScalarHaarRotation.scalar_measurable D (U p)) D.upper
            (ScalarHaarRotation.scalar_bound D (U p)) (ScalarHaarHeatRows.test (T-(p.1:ℝ)) x),0)
        else 0) := by
  let a := additiveRow 𝓕 μ H D ht x
  let r := residualRow 𝓕 μ H D U hU ht x
  have ha := NativeObservationProcess.process_ae 𝓕 μ H
    (sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D)) (sq_nonneg _)
    (fun _ => AdditiveHaarForcing.constantField ((ScalarHaarRotation.amplitude D)^2)
      (sq_pos_of_pos (ScalarHaarRotation.amplitude_pos D))) stronglyMeasurable_const ht x
  have hr := NativeObservationProcess.process_ae 𝓕 μ H D.ell_pos D.cap_nonneg
    (residual D U) (residual_predictable 𝓕 D U hU) ht x
  filter_upwards [PredictableItoRotation.processIsometry_ae 𝓕 μ H (field D U)
    (field_measurable 𝓕 D U hU) (TwoChannelItoRows.block 𝓕 μ H a r),
    TwoChannelItoRows.block_ae 𝓕 μ H a r,ha,hr] with p hm hb ha hr
  change a p = _ at ha
  change r p = _ at hr
  change originalRow 𝓕 μ H D U hU ht x p = _
  change originalRow 𝓕 μ H D U hU ht x p = field D U p (TwoChannelItoRows.block 𝓕 μ H a r p) at hm
  rw [hm,hb]
  change field D U p (WithLp.toLp 2 (a p,r p)) = _
  rw [ha,hr,NativeObservationProcess.integrand_eq _ _ ht x p,NativeObservationProcess.integrand_eq _ _ ht x p]
  by_cases hp : (p.1:ℝ) < t
  · rw [if_pos hp,if_pos hp,if_pos hp]
    exact ScalarHaarHeatRows.analysis D (U p) (hp.trans ht) x
  · rw [if_neg hp,if_neg hp,if_neg hp]
    change (ScalarHaarRotation.rotation D (U p)) (0 : Both RealHaarInput) = 0
    exact map_zero _
end SHE.PredictableScalarHaarRotation
