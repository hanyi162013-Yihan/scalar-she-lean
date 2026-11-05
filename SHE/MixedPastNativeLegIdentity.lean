module
public import SHE.ControlledFamilyNativeCovariancePacket
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.MixedPastNativeCovariance
public import SHE.NativeReserveRowEnvelope

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeLegIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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


local instance mixedPastLiteralCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open scoped BigOperators
local instance mixedPastLiteralCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Point"=>MixedPastNativeCovariance.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "R"=>ControlledFamilyNativeLegs.reserve P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Cov"=>ControlledFamilyNativeLegs.covarianceLeg P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm

local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- The mean in the canonical three-leg FTC is exactly the native
random-past joint mean used by the literal conditional omitted words. -/
theorem mean_eq_meanField
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (k : ℕ) (h : History X k) (θ : ℝ) (q : ℝ≥0)
    (hq : (q:ℝ)<(carrier Zero k).terminal h) (ω : Ω) :
    ControlledFamilyActualTransfer.mean P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ=
      Mean k θ q ω h := by
  unfold ControlledFamilyActualTransfer.mean ControlledFamilyThreeLeg.center
  rw [ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k h]
  have he:=MixedPastLiteralMean.meanField_eq_jointMeanVector
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hages hrootStop k h θ q hq ω
  have hT : CoveredControlledLaw.targets Zero k h=(fun i=>((carrier Zero k).observations.observations h i).target):=rfl
  have hC : CoveredControlledLaw.centers Zero k h=(fun i=>((carrier Zero k).observations.observations h i).center):=rfl
  rw [hT,hC] at he
  exact he.symm


/-- The first-score reserve is independent of every selected past state
and theta, and equals the original physical reserve at Zero. -/
theorem reserve_eq_zero
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (p:Inputs) (θ:ℝ) (k:ℕ) (h:History X k) (q:ℝ):
    R p k h q=NativeFirstScoreReserve.covariance P
      (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
      (centers Zero k h) (q-(v:ℝ)):=by
  rw [←ControlledFamilyNativeWordIdentity.reserve_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm hroot p θ,
    ControlledThetaRelativeDerivative.stops_eq P haP Λ v b hvb Z htarget hstop F hF hFm (θ,p) (0,(0,0)) k h,
    ControlledThetaRelativeDerivative.targets_eq P haP Λ v b hvb Z htarget hstop F hF hFm (θ,p) (0,(0,0)) k h,
    ControlledThetaRelativeDerivative.centers_eq P haP Λ v b hvb Z htarget hstop F hF hFm (θ,p) (0,(0,0)) k h,
    ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q]

/-- Actual native-family covariance contribution equals the exact
random-state point whose sharp profile A energy is already proved.
The history event is common before every random substitution. -/
theorem covariance_leg_eq_point_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀θ:ℝ,∀q:ℝ≥0,v≤q→(q:ℝ)<(carrier Zero k).terminal h→
      ∀E:WordRecursion.State (n+k),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
        (centers Zero k h) ((q:ℝ)-(v:ℝ)))).range→
      ∀ω:Ω,Cov (U ω,Dir ω) k h q (embed (S.first q ω))
        (embed (S.second q ω-S.first q ω)) E θ=Point k θ q h E ω:=by
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hroot x i]
    exact htarget x i
  have hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ):=fun x i=>(hroot x i).le
  filter_upwards [ControlledFamilyNativeCovariancePacket.covariance_leg_eq_packet_all_parameters_ae
    P haP Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hh
  intro θ q hvq hqt E hE ω
  have hqt':(q:ℝ)<(carrier (Base (0,(U ω,Dir ω))) k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k]
    exact hqt
  have hE':E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (R (U ω,Dir ω) k h q)).range:=by
    rw [reserve_eq_zero Λ P haP v b hvb Z htarget hstop F hF hFm hroot (U ω,Dir ω) θ]
    exact hE
  rw [hh (U ω,Dir ω) θ q (by exact_mod_cast hvq) hqt'
    (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E hE',
    mean_eq_meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h θ q hqt ω]
  rfl

end SHE.MixedPastNativeLegIdentity
