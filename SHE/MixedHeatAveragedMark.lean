module

public import SHE.MixedJointMarkConvergence
public import SHE.WeightedHistoryL2Limit
public import SHE.JointRecursiveHessian
public import SHE.NativeRowTargetContinuity
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedHeatAveragedMark
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open scoped ENNReal NNReal
local instance mixedJointMarkConvergenceInstance1 : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance mixedJointMarkConvergenceInstance2 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedJointMarkConvergenceInstance3 : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance mixedJointMarkConvergenceInstance4 : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance mixedJointMarkConvergenceInstance5 : MeasurableSpace CircleL2 := borel _
local instance mixedJointMarkConvergenceInstance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedJointMarkConvergenceInstance7 : MeasurableSpace RealL2 := borel _
local instance mixedJointMarkConvergenceInstance8 : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

open CutoffWordHistories RecursiveHeatBounds RecursiveHeatTargets Filter Topology
variable (δ : ℝ) (hδ : 0<δ)

local notation "Mmark" => MixedJointMarkLimit.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ
local notation "D" => MixedJointLevelData.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "I" => fun ε k => JointWordDefect.integrand (level L δ hδ ε k) Λ U V XU XV (D (level L δ hδ ε k))


/-- Actual first-defect marks converge in sample L2 after averaging
the original finite histories. The heat parameter changes the entire
recursive test; no uniform delta or depth limit is asserted. -/
theorem mark_limit (hΛ:0≤Λ) (ν:Measure P) [IsFiniteMeasure ν] (k:ℕ):
    let E:=fun ε:ℝ=>fun ω=>∫p,Mmark ε.toNNReal k p ω-Mmark 0 k p ω ∂historyMeasure R ν k
    (∀ε,Integrable (fun ω=>‖E ε ω‖^2) μ) ∧
      Tendsto (fun ε=>∫ω,‖E ε ω‖^2 ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0):=by
  obtain ⟨C,hC,hCb⟩:=MixedJointMarkConvergence.uniform_mark_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ k
  have hm(ε:ℝ≥0):Measurable (fun z:History P k×Ω=>Mmark ε k z.1 z.2):=
    MixedJointLevelData.mark_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (level L δ hδ ε k)
  exact WeightedHistoryL2Limit.averaged_limit (historyMeasure R ν k) μ
    (fun ε:ℝ=>fun z:History P k×Ω=>Mmark ε.toNNReal k z.1 z.2)
    (fun z=>Mmark 0 k z.1 z.2) (fun ε=>hm ε.toNNReal) (hm 0)
    (fun _=>1) (integrable_const 1) (fun _=>by norm_num) hC
    (fun ε p ω=>by simpa only [mul_one] using hCb ε.toNNReal p ω)
    (fun p ω=>by simpa only [mul_one] using hCb 0 p ω)
    (𝓝[>] (0:ℝ)) (by
      simpa only [Real.norm_eq_abs] using
        MixedJointMarkConvergence.integrated_mark_difference_tendsto_zero
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ hΛ ν k)

end SHE.MixedHeatAveragedMark
