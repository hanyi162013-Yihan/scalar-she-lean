module
public import SHE.ControlledFamilyNativeBaselinePacket
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.MixedPastNativeBaselineLeaf

public import SHE.MixedPastProfileDerivative
public import SHE.MixedPastOmittedMarkFields
public import SHE.MixedPastLiteralOmitted
public import SHE.MixedPastNativeOmitted
public import SHE.ControlledThetaOmittedFields
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.MixedPastLiteralFields
public import SHE.JointInterpolationFields
public import SHE.WeightedRowTimeShift
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

namespace SHE.MixedPastNativeBaselineIdentity
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastOmittedLeafMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastOmittedLeafMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastOmittedLeafMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastOmittedLeafMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastOmittedLeafMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastOmittedLeafMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
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


local instance mixedPastOmittedLeafMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastOmittedLeafMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastOmittedLeafMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v


local notation "Leg"=>ControlledFamilyNativeLegs.baselineLeg P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Value"=>MixedPastNativeBaselineLeaf.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Exact actual-solution baseline component, with every correlated
original leaf multiplier and full native omitted packet retained. -/
theorem baseline_leg_eq_neg_sum_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀θ:ℝ,∀q:ℝ≥0,v≤q→(q:ℝ)<(carrier Zero k).terminal h→
      ∀E:WordRecursion.State (n+k),∀ω:Ω,
      Leg (U ω,Dir ω) k h q (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E θ=
        -(∑j:Fin k,Value k θ q h E j ω):=by
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hroot x i]
    exact htarget x i
  have hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ):=fun x i=>(hroot x i).le
  filter_upwards [ControlledFamilyNativeBaselinePacket.baseline_leg_eq_packet_all_parameters_ae
    P haP Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hh
  intro θ q hvq hqt E ω
  have hqt':(q:ℝ)≤(carrier (Base (0,(U ω,Dir ω))) k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm (0,(U ω,Dir ω)) (0,(0,0)) k]
    exact hqt.le
  rw [hh (U ω,Dir ω) θ q (by exact_mod_cast hvq) hqt'
    (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) E,
    MixedPastBaselineFTCIdentity.mean_eq_meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k h θ q hqt ω]
  unfold ControlledFamilyNativeBaselinePacket.packet MixedPastNativeBaselineLeaf.value
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [MixedPastBaselineIdentity.baseline_derivative_eq_leaf_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb Z htarget hstop F hF hFm]
  rfl

end SHE.MixedPastNativeBaselineIdentity
