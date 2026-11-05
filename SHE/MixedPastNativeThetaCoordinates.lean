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

public import SHE.MixedPastNativeThetaRMSFields
public import SHE.MixedPastNativeCovarianceMass
public import SHE.MixedPastDerivativeRMS
@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeThetaCoordinates
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


local notation "Mass"=>MixedPastNativeThetaRMSFields.mass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RelativeMass"=>MixedPastNativeCovarianceMass.scoreMass
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The actual mass on original histories is EXACTLY the relative
field whose genuine joint theta/output energy was checked. -/
theorem mass_relative
    (hrootTarget:∀x i,(Z.observations x i).target=(b:ℝ))
    (hrootStop:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
    (k:ℕ)(θ:ℝ)(q:ℝ≥0)(t:Fin k→ℝ)(w:Fin k→HeatCircle)(x:HeatCircle)(ω:Ω):
    Mass k θ q (separated k (x,t,fun i=>w i+x)) ω=
      RelativeMass k θ q t ((ω,x),w):=by
  let h:=separated k (x,t,fun i=>w i+x)
  let a:=QuarterSpatialEvent.anchor k t
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have ht:targets Zero k h=targets Zero k a:=
    FixedHistoryTimeFactors.targets_sections Zero b hT (fun _:Fin 1=>(b:ℝ)) hrootTarget k t x 0 _ _
  have hs:stops Zero k h=stops Zero k a:=
    ScalarRootRelativeGeometry.covered_stops_sections Zero b hT (b:ℝ) hrootStop k t x 0 _ _
  have hl:lower Zero k h=lower Zero k a:=FixedHistoryTimeFactors.lower_sections Zero b hT k t x 0 _ _
  have hu:upper Zero k h=upper Zero k a:=FixedHistoryTimeFactors.upper_sections Zero b hT k t x 0 _ _
  have hc:=ScalarRootRelativeGeometry.centers_relative Zero hcenter k t x w
  change centers Zero k h=_ at hc
  change Mass k θ q h ω=_
  simp only [MixedPastNativeThetaRMSFields.mass,ht,hs,hl,hu,hc,
    MixedPastNativeCovarianceMass.scoreMass,a]

/-- Original old spatial coordinates have their literal entries; this
identity is independent of any scalar-root coefficient or stochastic law. -/
theorem space_separated {Y:Type}[MeasurableSpace Y](k:ℕ)(x:Y)
    (t:Fin k→ℝ)(z:Fin k→HeatCircle):space k (separated k (x,t,z))=z:=by
  induction k with
  | zero=>funext j;exact Fin.elim0 j
  | succ k ih=>
    funext j
    refine Fin.cases rfl (fun i=>?_) j
    exact congrFun (ih (fun j=>t j.succ) (fun j=>z j.succ)) i

/-- The erased baseline keeps the FULL original age and its original
translated leaf location before sample RMS or theta averaging. -/
theorem leaf_relative (k:ℕ)(θ:ℝ)(t:Fin k→ℝ)(w:Fin k→HeatCircle)
    (x:HeatCircle)(j:Fin k)(ω:Ω):
    MixedPastOmittedMarkFields.leafInput
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
      k θ (separated k (x,t,fun i=>w i+x)) j ω=
    MixedPastDerivativeRMS.field
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v
      (targets Zero k (QuarterSpatialEvent.anchor k t) (leafIndex k (fun i=>i) j)-(v:ℝ)) θ (ω,x+w j):=by
  let h:=separated k (x,t,fun i=>w i+x)
  let a:=QuarterSpatialEvent.anchor k t
  have hT:∀x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hl:lower Zero k h=lower Zero k a:=FixedHistoryTimeFactors.lower_sections Zero b hT k t x 0 _ _
  have ht:targets Zero k a (leafIndex k (fun i=>i) j)=lower Zero k a j:=by
    rw [targets,leaf_observation Zero k a j]
  have hsp:=congrFun (space_separated k x t (fun i=>w i+x)) j
  change space k h j=_ at hsp
  simp only [MixedPastOmittedMarkFields.leafInput,MixedPastDerivativeRMS.field,
    MixedPastJointData.pastU,MixedPastJointData.pastD]
  change ControlledProfile.derivative P Λ (embed (S.first v ω)) (embed (S.second v ω-S.first v ω))
    ((lower Zero k h j-(v:ℝ),space k h j),θ)=_
  rw [hl,hsp,add_comm (w j) x,ht]

end SHE.MixedPastNativeThetaCoordinates
