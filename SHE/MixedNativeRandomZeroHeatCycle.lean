module

public import SHE.MixedNativeRandomRecursiveIdentity
public import SHE.MixedNativeRandomZeroHeatExpectation
public import SHE.NodeIntegralCycle
public import SHE.MixedNativeRandomHeatAnalyticLimit
public import SHE.ControlledReferenceRandomHeatLeafLimit
public import SHE.FiniteWordExpectation
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

namespace SHE.MixedNativeRandomZeroHeatCycle
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
local instance mixedNativeRandomZeroHeatCycle_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Leaf" => (fun p ε k => MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
local notation "Ref" => (fun p ε k => MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
local notation "Loc" => (fun p ε k => MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))
local notation "Mark" => (fun p ε k => MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k))

open Filter Topology
local notation "Base" => ControlledReferenceLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF

local notation "R₀" => ControlledReferenceLevel.referenceData P (fun z => κ+aV z) hAs Λ θ v b hvb (0,0)

local notation "node" => CutoffWordHistories.nodeMeasure R₀
local instance mixedNativeRandomZeroHeatCycle_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeRandomZeroHeatCycle_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeRandomZeroHeatCycle_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeRandomZeroHeatCycle_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ hsmall in
/-- Exact arbitrary-past random-reference cycle after the spatial heat
regularization has been removed. Only the explicit terminal time-strip
correction remains, with the retained common-Haar mark terminating its
branch. This is an actual finite smooth-word identity on every F_v event. -/
theorem expected_cycle (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hP : P.coefficient=(fun z => κ+aV z)) (hbH : b≤H)
    (hwindow : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ν : Measure Unit) [IsFiniteMeasure ν] {η : ℝ} (hη : 0<η)
    (hgap : ∀ i,η≤(Z i).target-(b:ℝ)) (k : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ q : CutoffWordHistories.History Unit k×Ω,Leaf (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))=
    (∫ q : CutoffWordHistories.History Unit k×Ω,Ref (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))+
    (∫ q : CutoffWordHistories.History Unit k×Ω,Mark (pastParameter q.2) 0 k q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A))+
    (∫ q : CutoffWordHistories.History Unit (k+1)×Ω,Leaf (pastParameter q.2) 0 (k+1) q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν (k+1)).prod (μ.restrict A))+
    (∫ q : CutoffWordHistories.History Unit k×Ω,
      JointCutoffStep.correction (L (pastParameter q.2) 0 k) Λ δ U V XU XV q.1 q.2
      ∂(CutoffWordHistories.historyMeasure R₀ ν k).prod (μ.restrict A)) := by
  let νk := CutoffWordHistories.historyMeasure R₀ ν k
  have hs := MixedNativeRandomZeroHeatExpectation.expected_zero_heat_level 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hJ hlocal hΛ hP hbH hwindow ν hη hgap k A hA
  have hl := (MixedNativeRandomRecursiveIdentity.pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ 0 k νk A).2.2.1
  have hn := (MixedNativeRandomRecursiveIdentity.pieces_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ 0 (k+1) (CutoffWordHistories.historyMeasure R₀ ν (k+1)) A).1
  let f := fun (h : CutoffWordHistories.History Unit k) (z : ℝ×HeatCircle) (ω : Ω) => Leaf (pastParameter ω) 0 (k+1) (h,z) ω
  have hi : Integrable (fun q : (CutoffWordHistories.History Unit k×Ω)×(ℝ×HeatCircle) => f q.1.1 q.2 q.1.2)
      ((νk.prod (μ.restrict A)).prod node) := by
    have hm := MeasurePreserving.symm (NodeIntegralCycle.cycle (A := CutoffWordHistories.History Unit k) (N := ℝ×HeatCircle) (Ω := Ω))
      (NodeIntegralCycle.measurePreserving_cycle νk node (μ.restrict A))
    exact hm.integrable_comp_of_integrable hn
  have hc := NodeIntegralCycle.integral_cycle_iterated νk node (μ.restrict A) f hi
  have hsplit := integral_sub hl hi.integral_prod_left
  have heq (q : CutoffWordHistories.History Unit k×Ω) :
      Loc (pastParameter q.2) 0 k q.1 q.2-∫ z,f q.1 z q.2 ∂node=
      JointCutoffStep.correction (L (pastParameter q.2) 0 k) Λ δ U V XU XV q.1 q.2 := by
    unfold JointCutoffStep.correction
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    change JointCutoffStep.heatChildLeaf (L (pastParameter q.2) 0 k) Λ δ U V XU XV 0 (q.1,z) q.2=_
    exact JointHeatLeafLimit.heatChild_zero_eq_literal δ Λ _ U V XU XV (q.1,z) q.2
  simp only [Pi.sub_apply] at hsplit
  rw [← hc] at hsplit
  have heint := integral_congr_ae (μ := νk.prod (μ.restrict A)) (Filter.Eventually.of_forall heq)
  have hsplit' : (∫ q : CutoffWordHistories.History Unit k×Ω,
      JointCutoffStep.correction (L (pastParameter q.2) 0 k) Λ δ U V XU XV q.1 q.2 ∂νk.prod (μ.restrict A))=
      (∫ q : CutoffWordHistories.History Unit k×Ω,Loc (pastParameter q.2) 0 k q.1 q.2 ∂νk.prod (μ.restrict A))-
      (∫ q : CutoffWordHistories.History Unit (k+1)×Ω,Leaf (pastParameter q.2) 0 (k+1) q.1 q.2
        ∂(CutoffWordHistories.historyMeasure R₀ ν (k+1)).prod (μ.restrict A)) := heint.symm.trans hsplit
  linarith only [hs,hsplit']

end SHE.MixedNativeRandomZeroHeatCycle
