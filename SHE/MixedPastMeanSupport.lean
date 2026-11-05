module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.MixedPastMeanInputEnergy
public import SHE.NativeKernelReindex
public import SHE.NativeKernelFiber
public import SHE.WeightedNoiseSupport

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanSupport
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanSupport_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanSupport_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanSupport_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanSupport_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanSupport_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanSupport_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanSupport_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanSupport_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanSupport_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPastMeanSupport_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Input" => MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastLiteralPoint.meanField MixedPastJointData.pastU MixedPastJointData.pastD

/-- Exact inactive-domain support of the actual random-reference mean
input. The profile remains evaluated at the same random past sample. -/
theorem input_zero_of_not_active (k : ℕ) (θ : ℝ) (q : ℝ≥0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ha : ¬active Zero (b:ℝ) k q t) (ω : Ω) :
    Input k θ q mass ρ hmass hρ t ω=0 := by
  let a : ℝ×Inputs:=(θ,(U ω,Dir ω))
  have hs : StrictHistory (Base a) k (anchor k t)↔StrictHistory Zero k (anchor k t) :=
    ControlledThetaPhysicalGeometry.strict_iff P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      a (0,(0,0)) k (anchor k t)
  have ha' : ¬active (Base a) (b:ℝ) k q t := by
    intro h
    have ht:=ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
      a (0,(0,0)) k (anchor k t)
    have hta:=terminal_separated (Base a) (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    have htz:=terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    have he:=hta.symm.trans (ht.trans htz)
    exact ha ⟨hs.mp h.1,by rw [←he];exact h.2⟩
  have hzero (y x : HeatCircle) :
      MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q q t (ω,(y,x))=0 := by
    exact weightedSpatial_zero_of_not_active (Base a) (b:ℝ) (fun _=>rfl) k Λ q q t
      (fun _ : Unit=>Mean k θ q ω) ha' () y x
  unfold MixedPastMeanInputEnergy.input
  rw [integralOperator_eq_zero_of_fiber _ ω hzero]
  simp only [ContinuousLinearMap.zero_apply,map_zero]

end SHE.MixedPastMeanSupport
