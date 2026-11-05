module

public import SHE.OffsetBudgetWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedPastJointData
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastOffsetWeights
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOffsetWeights_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOffsetWeights_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOffsetWeights_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOffsetWeights_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOffsetWeights_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOffsetWeights_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile

variable (θ : ℝ)

local instance mixedPastOffsetWeights_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOffsetWeights_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

include hIJ₀ hIJ₁ in
/-- The ACTUAL native current-offset Gaussian constant may be multiplied
by an arbitrary past-measurable energy, including the square of a random
covariance-profile score mass. Only conditional BDG on genuine past
events is used; no random Gaussian covariance is substituted into a
fixed-law probability-space estimate. -/
theorem constant_with_past_weight (P : CanonicalCovariance.ProfileParameters)
    (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (leaf : Fin m→Fin n) (hnative : ∀ j,σ (leaf j)=target (leaf j))
    (hage : ∀ j,0<target (leaf j)) (hgap : ∀ j,(q:ℝ)-(v:ℝ)<target (leaf j))
    (choices : List (Fin r×Fin (m+1))) (b : ℕ) (hb : 0<b)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (b*(m+2)) J B0)
    (weight : Ω→ℝ) (hw : Measurable[𝓕 v] weight) (hw0 : ∀ ω,0≤weight ω)
    (hwi : Integrable weight μ) :
    let U := MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir := MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean := MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let budget := fun ω=>currentBudget P Λ (U ω) (dir ω) θ target center leaf (mean ω) b
    Integrable (fun ω=>weight ω*constant P r m choices b (budget ω)) μ ∧
      (∫ ω,weight ω*constant P r m choices b (budget ω) ∂μ)≤
        constant P r m choices b
          ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
            (∫ ω,weight ω ∂μ) := by
  intro U dir mean budget
  let offset : Ω→Fin m→ℝ := fun ω j=>mean ω (leaf j)-
    ControlledProfile.mean Λ (U ω) (dir ω) (θ,(target (leaf j),center (leaf j)))
  have hU : Measurable U := (MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir : Measurable dir := (MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm := MixedPastJointData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hoffset : Measurable offset := by
    apply Measurable.of_eval
    intro j
    have hbase : Measurable (fun ω=>ControlledProfile.mean Λ (U ω) (dir ω)
        (θ,(target (leaf j),center (leaf j)))) := by
      convert! (ControlledProfile.meanFamily_measurable Λ).comp
        (((hU.prodMk hdir).prodMk measurable_const).prodMk
          (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
    exact (((EuclideanSpace.proj (𝕜:=ℝ) (leaf j)).continuous.measurable).comp hm).sub hbase
  have hevent (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) (j : Fin m) :=
    MixedPastJointData.native_leaf_moment_on_past_event
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ hlocal hΛ hθ
      v q hvq hqH hspan σ target center (leaf j) (hnative j) (hage j) (hgap j)
      (b*(m+2)) (Nat.mul_pos hb (by omega)) B0 hBDG P.exponent_pos.le P.exponent_le_one A hA
  have hM : 0≤M := hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hC : 0≤NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M := by
    unfold NativeHybridMoments.momentConstant
    exact mul_nonneg B0.2 (pow_nonneg
      (mul_nonneg ProfileVariance.upperConstant_pos.le (by positivity)) _)
  have hh := weighted_offset_constant μ (𝓕.le v) P b choices (fun j=>target (leaf j)) hage
    offset hoffset (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ((b*(m+2):ℕ)*P.exponent/2)
    ((NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)
    (Real.rpow_nonneg hC _) (fun A hA j=>hevent A hA j) weight hw hw0 hwi
  simpa only [budget,currentBudget,offset] using hh

end SHE.MixedPastOffsetWeights

