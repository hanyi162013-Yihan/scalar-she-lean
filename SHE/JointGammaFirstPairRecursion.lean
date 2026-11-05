module

public import SHE.JointGammaOrdinaryRetained
public import SHE.JointUncutSuccessor
public import SHE.OrdinaryJointSelf
public import SHE.JointGammaRetainedRecursion
public import SHE.JointGammaEndpointDrift
public import SHE.FiniteItoParameterResidual
public import SHE.JointGammaRecursionRows
public import SHE.JointGammaRecursionState
public import SHE.ControlledReferenceLevel
public import SHE.MixedJointUncutMark
public import SHE.ActualUncutRemainder
public import SHE.FirstGammaEndpointMappedRows
public import SHE.JointGammaDriftAlgebra
public import SHE.JointGammaTestFields
public import SHE.FiniteReferenceSpliceRows
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaEndpointCovariance
public import SHE.FiniteAffineRows
public import SHE.PredictableRealSections
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.JointGammaFirstPairRecursion
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointDrift_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointDrift_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointDrift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointDrift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointDrift_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointDrift_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointDrift_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointDrift_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


open Set FiniteCovariancePullback SmoothCylinders GaussianConvolution GaussianItoTest
variable (hvb:v≤b)(hstop:∀ i,(Z i).stop=(Z i).target)
variable {F:WordRecursion.State n→ℝ}(hF:BoundedSmooth F)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hH:(H:ℝ)≤1)(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Past"=>MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "hs"=>(fun i=>(htarget i).trans_eq (hstop i).symm)
local notation "Level" θ:max p:max=>ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hs F hF p
local notation "W" θ:max p:max=>ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "Y" θ:max=>FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ
local notation "Rows" θ:max=>FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "G" θ:max=>JointGammaTestFields.value P Λ θ v b hvb Z htarget F
local notation "dG" θ:max=>JointGammaTestFields.derivative P Λ θ v b hvb Z htarget F
local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "StateJ"=>MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z
local notation "Defect"=>MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z

open CutoffWordHistories
local notation "RefData" θ:max p:max=>ControlledReferenceLevel.referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p

def jointLeaf (ω:Ω):ℝ:=∫h:History Unit 1,
  JointUncutWordEvaluation.leaf (Level 1 (Past ω)) Λ
    (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField 1 h ω
    ∂historyMeasure (RefData 1 (Past ω)) (Measure.dirac ()) 1

def ordinaryLeaf (ω:Ω):ℝ:=∫h:History Unit 1,
  JointUncutWordEvaluation.leaf (Level 0 (Past ω)) 0
    (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField 1 h ω
    ∂historyMeasure (RefData 0 (Past ω)) (Measure.dirac ()) 1

def ordinaryError (ω:Ω):ℝ:=
  ActualUncutRemainder.value (Level 0 (Past ω)) (fun z=>κ+aU z)
    (DU).physicalState (DU).physicalField 0 () ω-
  ActualUncutRemainder.value (Level 0 (Past ω)) (fun z=>κ+aV z)
    (DU).physicalState (DU).physicalField 0 () ω

def firstMark (ω:Ω):ℝ:=MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
  I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) 0 () ω

/-- The joint local remainder is the literal next uncut leaf, on its
original absolute history measure, before any sample expectation. -/
theorem joint_remainder_eq_leaf(ω:Ω):
    MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S (Level 1 (Past ω)) () ω=
    jointLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω:=by
  have hnext:=JointUncutSuccessor.averaged_eq (Level 1 (Past ω)) Λ
    (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField
    (DU).physicalState_measurable (DV).physicalState_measurable
    (DU).physicalField_measurable (DV).physicalField_measurable (Measure.dirac ()) 0 ω
  change (∫p:Unit,JointUncutLocalRemainder.value (Level 1 (Past ω)) Λ
      (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField 0 p ω ∂Measure.dirac ())=_ at hnext
  rw [integral_dirac] at hnext
  simp only [JointUncutLocalRemainder.value,UncutSmoothWords.weight,one_mul] at hnext
  convert! hnext using 1 <;> rfl

/-- The companion insertion along the genuine ordinary-U state is its
literal next ordinary leaf, retaining the original profile and times. -/
theorem ordinary_remainder_eq_leaf(ω:Ω):
    ActualUncutRemainder.value (Level 0 (Past ω)) (fun z=>κ+aV z)
      (DU).physicalState (DU).physicalField 0 () ω=
    ordinaryLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω:=by
  have hnext:=JointUncutSuccessor.averaged_eq (Level 0 (Past ω)) 0
    (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField
    (DU).physicalState_measurable (DU).physicalState_measurable
    (DU).physicalField_measurable (DU).physicalField_measurable (Measure.dirac ()) 0 ω
  change (∫p:Unit,JointUncutLocalRemainder.value (Level 0 (Past ω)) 0
      (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField 0 p ω ∂Measure.dirac ())=_ at hnext
  rw [integral_dirac,OrdinaryJointSelf.uncutLocalRemainder] at hnext
  exact hnext

include hH B hBDG hIJ₀ hIJ₁ in
/-- Exact first-pair drift-to-recursion attachment. The ordinary rough
coefficient discrepancy remains positive in Ret0; the whole joint mark
is subtracted in Ret0 minus Ret1. -/
theorem retained_pair(hb0:0<b):∀ᵐω∂μ,
    JointGammaRetainedRecursion.retained (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb 0 ω-
    JointGammaRetainedRecursion.retained (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb 1 ω=
    ordinaryError 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω+
    ordinaryLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω-
      (firstMark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω+
       jointLeaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω):=by
  have h0:=JointGammaOrdinaryRetained.zero_eq_actual_remainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb hstop hF hAs hH B hBDG hIJ₀ hIJ₁ hb0
  have h1:=JointGammaRetainedRecursion.one_eq_mark_remainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb hstop hF hAs hH B hBDG hIJ₀ hIJ₁ hb0
  filter_upwards [h0,h1] with ω h0 h1
  have hj:=joint_remainder_eq_leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω
  have hu:=ordinary_remainder_eq_leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P v b htarget hvb hstop hF hAs ω
  rw [h0,h1,hj]
  unfold ordinaryError firstMark
  rw [hu]
  ring
end SHE.JointGammaFirstPairRecursion
