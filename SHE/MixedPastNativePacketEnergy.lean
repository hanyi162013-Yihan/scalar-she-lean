module

public import SHE.MixedPastNativeFirstWholeCompleteWeights
public import SHE.MixedPastTwoFreshCompleteWeights
public import SHE.ControlledFutureFields
public import SHE.SectionEnergy
public import SHE.NativeFirstWholeComplete
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

namespace SHE.MixedPastNativePacketEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativePacketEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativePacketEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativePacketEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativePacketEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativePacketEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativePacketEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPastNativePacketEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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


local instance mixedPastNativePacketEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativePacketEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
open GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  NativeFirstWholeMoments GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
variable {n d r m : ℕ}

/-- Literal actual joint mean at variable theta and translated output. -/
def meanField (v q:ℝ≥0) (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle)
    (z:ℝ×(Ω×UnitAddCircle)):State n:=
  MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.1 v q σ target
    (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2.2)) z.2.1

theorem meanField_measurable (v q:ℝ≥0) (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle)
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i):
    Measurable (meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q σ target a):=by
  have hu:Measurable (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q):=
    (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q).mono (𝓕.le q) le_rfl
  have hd:Measurable (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q):=
    (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S q).mono (𝓕.le q) le_rfl
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hc:Measurable (fun z:ℝ×(Ω×UnitAddCircle)=>StoppedGaussianScore.nativeCenter (fun j=>a j+z.2.2) i):=
    (CircleNormalization.continuous_scale 1 (2*Real.pi)).measurable.comp
      (measurable_const.add measurable_snd.snd)
  have hcur:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hu.comp measurable_snd.fst).prodMk ((measurable_const (a:=target i+(v:ℝ)-(q:ℝ))).prodMk hc))
  have hdir:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hd.comp measurable_snd.fst).prodMk ((measurable_const (a:=target i+(v:ℝ)-(q:ℝ))).prodMk hc))
  have ht:0<target i+(v:ℝ)-(q:ℝ):=by linarith [hgap i]
  change Measurable (fun z:ℝ×(Ω×UnitAddCircle)=>
    functional (target i+(v:ℝ)-(q:ℝ)) (StoppedGaussianScore.nativeCenter (fun j=>a j+z.2.2) i) (S.first q z.2.1)+
      z.1*Real.exp (-Λ*(σ i+(v:ℝ)-(q:ℝ)))*functional (target i+(v:ℝ)-(q:ℝ))
        (StoppedGaussianScore.nativeCenter (fun j=>a j+z.2.2) i) (S.second q z.2.1-S.first q z.2.1))
  simp_rw [NativeHeatObservation.functional_physical ht]
  exact hcur.add ((measurable_fst.mul_const _).mul hdir)

/-- Actual full-age offset budget, before any Gaussian law is averaged. -/
def budget (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0) (σ target:Fin n→ℝ)
    (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n) (p:ℕ)
    (z:ℝ×(Ω×UnitAddCircle)):ℝ:=
  NativeFirstWholeMoments.currentBudget P Λ
    (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.2.1)
    (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.2.1)
    z.1 target (StoppedGaussianScore.nativeCenter (fun i=>a i+z.2.2)) leaf
    (meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q σ target a z) p

theorem budget_measurable (P:CanonicalCovariance.ProfileParameters) (v q:ℝ≥0)
    (σ target:Fin n→ℝ) (a:Fin n→UnitAddCircle) (leaf:Fin m→Fin n) (p:ℕ)
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i):
    Measurable (budget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P v q σ target a leaf p):=by
  have hu:Measurable (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v):=
    (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hd:Measurable (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v):=
    (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm:=meanField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v q σ target a hgap
  unfold budget NativeFirstWholeMoments.currentBudget NormalizedLeafOffsets.budget
  apply Finset.measurable_sum
  intro j _
  have hc:Measurable (fun z:ℝ×(Ω×UnitAddCircle)=>StoppedGaussianScore.nativeCenter (fun i=>a i+z.2.2) (leaf j)):=
    (CircleNormalization.continuous_scale 1 (2*Real.pi)).measurable.comp
      (measurable_const.add measurable_snd.snd)
  have hp:Measurable (fun z:ℝ×(Ω×UnitAddCircle)=>ControlledProfile.mean Λ
      (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.2.1)
      (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v z.2.1)
      (z.1,(target (leaf j),StoppedGaussianScore.nativeCenter (fun i=>a i+z.2.2) (leaf j)))):=by
    convert! (ControlledProfile.meanFamily_measurable Λ).comp
      ((((hu.comp measurable_snd.fst).prodMk (hd.comp measurable_snd.fst)).prodMk measurable_fst).prodMk
        (measurable_const.prodMk hc)) using 1
  exact ((continuous_abs.measurable.comp (((EuclideanSpace.proj (𝕜:=ℝ) (leaf j)).continuous.measurable.comp hm).sub hp)).pow_const _).div_const _

end SHE.MixedPastNativePacketEnergy
