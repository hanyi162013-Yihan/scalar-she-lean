module

public import SHE.QuarterSpatialEvent
public import SHE.ScalarRootRelativeGeometry
public import SHE.NativeCurrentOutputEnergy
public import SHE.ControlledThetaNativePointFields
public import SHE.MixedPastLiteralFields
public import SHE.ControlledFamilyKernelBounds
public import SHE.NativeKernelParameterAverage
public import SHE.ControlledFamilyNativePacketFTC
public import SHE.MixedPastNativeLegIdentity
public import SHE.MixedPastNativeMeanClip
public import SHE.MixedPastNativeMeanCap
public import SHE.NativeCarrierGeometry
public import SHE.ControlledRelativeScoreForest
public import SHE.ControlledThetaNativeGradient
public import SHE.MixedPastNativeConsistentPoint
public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.NativeCurrentCoordinates
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanFTCClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanFTCClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanFTCClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanFTCClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanFTCClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastNativeMeanFTCClip_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeMeanFTCClip_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeMeanFTCClip_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

variable {m r : ℕ}

/-- The SAME actual endpoint packet at translated carrier centers is
its literal native-output evaluation; no stochastic law changes. -/
theorem packet_translate {N:ℕ} (q:ℝ≥0) (σ target:Fin N→ℝ) (a a':Fin N→UnitAddCircle)
    (x:UnitAddCircle) (he:(fun i=>a' i+(0:UnitAddCircle))=fun i=>a i+x)
    (leaf:Fin m→Fin N) (p:ℕ) (ω:Ω):
    MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (r:=r)
      P v q σ target a' leaf p (ω,0)=
    MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (r:=r)
      P v q σ target a leaf p (ω,x):=by
  simp only [MixedPastNativePacketUniform.packet,MixedPastNativePacketUniform.envelope,
    MixedPastNativePacketEnergy.budget,MixedPastNativePacketEnergy.meanField]
  rw [he]

/-- The varying-reserve current score has the same exact output
translation, retaining its ORIGINAL q-clock and all old fractions. -/
theorem amplitude_translate {N:ℕ} (q:ℝ≥0) (target:Fin N→ℝ) (lo hi:Fin r→ℝ)
    (a a':Fin N→UnitAddCircle) (x:UnitAddCircle)
    (he:(fun i=>a' i+(0:UnitAddCircle))=fun i=>a i+x) (ω:Ω):
    MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P v q target a' lo hi (ω,0)=
    MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P v q target a lo hi (ω,x):=by
  simp only [MixedNativeDampedScoreAmplitude.amplitude,MixedNativeDampedScoreAmplitude.score,
    MixedNativeDampedScoreEnergy.value]
  rw [he]

/-- All current score/offset factors in the physical relative-history
section equal the factors whose true joint native-output L² was proved. -/
theorem current_factor_relative
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:HeatCircle)
    (p:ℕ)(χ:ℝ)(ω:Ω):
    let h:=separated k (x,t,fun i=>w i+x)
    let a0:=QuarterSpatialEvent.anchor k t
    let target:=fun i=>targets Zero k a0 i-(v:ℝ)
    let lo:=fun j=>lower Zero k a0 j-(v:ℝ)
    let hi:=fun j=>upper Zero k a0 j-(v:ℝ)
    let a:=fun i=>NativeHeatSpan.unitCenter (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i)
    let ah:=fun i=>NativeHeatSpan.unitCenter (centers Zero k h i)
    (MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P v q (fun i=>targets Zero k h i-(v:ℝ)) ah (fun j=>lower Zero k h j-(v:ℝ))
      (fun j=>upper Zero k h j-(v:ℝ)) (ω,0))^χ*
      MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (r:=k)
        P v q (fun i=>targets Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) ah
        (leafIndex k (fun i=>i)) p (ω,0)=
    (MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P v q target a lo hi (ω,NativeHeatSpan.unitCenter x))^χ*
      MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (r:=k)
        P v q target target a (leafIndex k (fun i=>i)) p (ω,NativeHeatSpan.unitCenter x):=by
  intro h a0 target lo hi a ah
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have ht:targets Zero k h=targets Zero k a0:=
    FixedHistoryTimeFactors.targets_sections Zero b hT (fun _:Fin 1=>(b:ℝ)) hrootTarget k t x 0 _ _
  have hl:lower Zero k h=lower Zero k a0:=FixedHistoryTimeFactors.lower_sections Zero b hT k t x 0 _ _
  have hu:upper Zero k h=upper Zero k a0:=FixedHistoryTimeFactors.upper_sections Zero b hT k t x 0 _ _
  have ha:(fun i=>ah i+(0:UnitAddCircle))=fun i=>a i+NativeHeatSpan.unitCenter x:=by
    funext i
    rw [add_zero]
    change NativeHeatSpan.unitCenter (centers Zero k h i)=_
    rw [ScalarRootRelativeGeometry.centers_relative Zero hcenter]
    exact (CircleNormalization.scale (2*Real.pi) 1).map_add _ _
  simp only [ht,hl,hu]
  rw [amplitude_translate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v
      q target lo hi a ah (NativeHeatSpan.unitCenter x) ha ω,
    packet_translate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P v
      q target target a ah (NativeHeatSpan.unitCenter x) ha (leafIndex k (fun i=>i)) p ω]

set_option backward.isDefEq.respectTransparency false in
/-- The full old positive score forest is translated only in space.
Its genuine time weight and every original parent are unchanged. -/
theorem old_envelope_relative
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:HeatCircle)
    (hp:StrictHistory Zero k (separated k (x,t,fun i=>w i+x)))
    (hp0:StrictHistory Zero k (QuarterSpatialEvent.anchor k t)):
    timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k (separated k (x,t,fun i=>w i+x))*
      OrderedHeatForests.parentDensity 2 (by norm_num) k
        (targets Zero k (separated k (x,t,fun i=>w i+x)))
        (carrier_orderedTimes Zero hages k _ hp) (centers Zero k (separated k (x,t,fun i=>w i+x)))=
    timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k (QuarterSpatialEvent.anchor k t)*
      OrderedHeatForests.parentDensity 2 (by norm_num) k
        (targets Zero k (QuarterSpatialEvent.anchor k t)) (carrier_orderedTimes Zero hages k _ hp0)
        (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w):=by
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have ht:=FixedHistoryTimeFactors.targets_sections Zero b hT (fun _:Fin 1=>(b:ℝ)) hrootTarget
    k t x 0 (fun i=>w i+x) (fun _=>0)
  rw [FixedHistoryTimeFactors.timeWeight_sections Zero b hT _ _ k t x 0 _ (fun _=>0)]
  rw [ScalarRootRelativeGeometry.centers_relative Zero hcenter]
  have hpd (s t:Fin (1+k)→ℝ) (hs:OrderedHeatForests.OrderedTimes k s)
      (ht:OrderedHeatForests.OrderedTimes k t) (he:s=t):
      OrderedHeatForests.parentDensity 2 (by norm_num) k s hs
        (fun i=>OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w i+x)=
      OrderedHeatForests.parentDensity 2 (by norm_num) k t ht
        (OrderedHeatForests.values (fun _:Fin 1=>(0:HeatCircle)) k w):=by
    subst t
    exact ScalarRootRelativeGeometry.parentDensity_translate 2 (by norm_num) k s hs _ x
  exact congrArg (fun z:ℝ=>timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k
    (QuarterSpatialEvent.anchor k t)*z) (hpd _ _ _ _ ht)

end SHE.NativeCurrentCoordinates
