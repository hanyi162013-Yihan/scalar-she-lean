module

public import SHE.MixedNativeRandomRecursiveIdentity
public import SHE.MixedNativeRandomUncutLimits
public import SHE.MixedNativeRandomZeroHeatCycle
public import SHE.ControlledReferenceRandomCutoffEvaluationLimit
public import SHE.ControlledReferenceRandomCutoffCorrection
public import SHE.ControlledReferenceRandomMarkLimit
public import SHE.MixedJointUncutMark
public import SHE.ControlledReferenceUncutBounds
public import SHE.DominatedCutoffLimit
public import SHE.FiniteParameterL1Limit
public import SHE.JointRecursiveReferenceLimit
public import SHE.JointRecursiveRemainderConvergence
public import SHE.MixedJointMarkConvergence
public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveResidualContinuity
public import SHE.PastParameterHistoryExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedNativeRandomUncutExpansion
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeRandomUncutExpansion_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)


local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open Filter Topology
local notation "Base" => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF

open CutoffWordHistories
local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)

local notation "LM" => MixedNativeRandomUncutLimits.leafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "RM" => MixedNativeRandomUncutLimits.referenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "MM" => MixedNativeRandomUncutLimits.markMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CLM" => MixedNativeRandomUncutLimits.cutoffLeafMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CRM" => MixedNativeRandomUncutLimits.cutoffReferenceMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CMM" => MixedNativeRandomUncutLimits.cutoffMarkMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF
local notation "CM" => MixedNativeRandomUncutLimits.correctionMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF

local instance mixedNativeRandomUncutExpansion_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRandomUncutExpansion_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRandomUncutExpansion_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRandomUncutExpansion_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hsmall hIJ₀ hIJ₁ in
theorem recursive_step (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ν : Measure Unit) [IsFiniteMeasure ν] {η : ℝ} (hη : 0<η)
    (hgap : ∀ i,η≤(Z i).target-(b:ℝ)) (k : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    LM ν k A=RM ν k A+MM ν k A+LM ν (k+1) A := by
  have he : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ),CLM ν k A δ=CRM ν k A δ+CMM ν k A δ+CLM ν (k+1) A δ+CM ν k A δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0<δ at hδ
    have hs := MixedNativeRandomZeroHeatCycle.expected_cycle 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hJ hlocal hΛ hP hbH hwindow ν hη hgap k A hA
    simpa only [MixedNativeRandomUncutLimits.cutoffLeafMass,MixedNativeRandomUncutLimits.cutoffReferenceMass,
      MixedNativeRandomUncutLimits.cutoffMarkMass,MixedNativeRandomUncutLimits.correctionMass,
      JointUncutEvaluationLimit.cutoffLeaf,JointUncutEvaluationLimit.cutoffReference,MixedJointUncutMark.cutoffMark,
      ControlledReferenceRandomCutoffCorrection.mass,dif_pos hδ,ControlledReferenceRecursiveBounds.level,
      MixedJointLevelData.leaf,MixedJointLevelData.reference] using hs
  have ht := (((MixedNativeRandomUncutLimits.reference_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ν k A).add
    (MixedNativeRandomUncutLimits.mark_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ν k A)).add
    (MixedNativeRandomUncutLimits.leaf_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ν (k+1) A)).add
    (MixedNativeRandomUncutLimits.correction_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF ν k A)
  simp only [add_zero] at ht
  exact tendsto_nhds_unique (MixedNativeRandomUncutLimits.leaf_tendsto 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hsmall hΛ ν k A) (ht.congr' (Filter.EventuallyEq.symm he))

include hsmall hIJ₀ hIJ₁ in
/-- Actual arbitrary-past random-reference finite first-defect expansion
for the constructed mixed native pair, after removing BOTH recursively
moving cutoffs. The ORIGINAL F_v states determine the complete canonical
controlled reference and every test in the tree. The retained common-Haar
marks terminate branches. The terminal leaf remains at any chosen finite
depth; constants may depend on that depth and smooth coefficient jets.
No independent restart/random-reference formula or rough uniform limit
is assumed. The initial root heat gap remains explicit. -/
theorem finite_expected_expansion (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ν : Measure Unit) [IsFiniteMeasure ν] {η : ℝ} (hη : 0<η)
    (hgap : ∀ i,η≤(Z i).target-(b:ℝ)) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) (depth : ℕ) :
    LM ν 0 A=(∑ k∈Finset.range depth,RM ν k A)+(∑ k∈Finset.range depth,MM ν k A)+LM ν depth A := by
  induction depth with
  | zero => simp
  | succ d ih =>
    have hs := recursive_step 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hsmall J hIJ₀ hIJ₁ hnull hJ hlocal hΛ hP hbH hwindow ν hη hgap d A hA
    simp only [Finset.sum_range_succ]
    linarith only [ih,hs]

end SHE.MixedNativeRandomUncutExpansion
