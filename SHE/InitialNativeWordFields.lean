module

public import SHE.MixedPastTerminalRemainderEnergy
public import SHE.InitialTerminalFibre
public import SHE.ZeroDirectionProfile
public import SHE.MixedNativePairInitial
public import SHE.ControlledScalarReference
public import SHE.RelativePairedCurrent
public import SHE.PairedFamilyFields
public import SHE.MovingNativeFields
public import SHE.ShiftedHistoryMeasure
public import SHE.MixedPairedMovingSection
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPastTerminalPairedLinearEnergy
public import SHE.MixedPairedCurrentClock
public import SHE.MixedPastTerminalTimeFields
public import SHE.ControlledTerminalRMSMass
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.InitialNativeWordFields
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance initialNativeWordFields_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance initialNativeWordFields_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance initialNativeWordFields_instance3 : MeasurableSpace RealL2 := borel _
local instance initialNativeWordFields_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance initialNativeWordFields_instance5 : MeasurableSpace CircleL2 := borel _
local instance initialNativeWordFields_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance initialNativeWordFields_instance7 : MeasurableSpace RealHaarInput := borel _
local instance initialNativeWordFields_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance initialNativeWordFields_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance initialNativeWordFields_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance initialNativeWordFields_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance initialNativeWordFields_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth CutoffWordLevel
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient) (h:ℝ≥0)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R"=>ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (embed u₀,0)
local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "ZZ" T:max=>ControlledScalarReference.observations T
local notation "K" α:max T:max=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ α 0 T bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (embed u₀,0)
local notation "Zero" T:max=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ 0 0 T bot_le
  (ZZ T) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm (0,0)

def value (k:ℕ) (T:Icc (0:ℝ) (h:ℝ)) (ω:Ω):ℝ:=
  InitialTerminalFields.value R F hF hFm Λ (DU).physicalState (DV).physicalState
    (DU).physicalField (DV).physicalField k T ω

theorem value_measurable (k:ℕ):Measurable (fun z:Icc (0:ℝ) (h:ℝ)×Ω=>
    value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k z.1 z.2):=
  InitialTerminalFields.value_measurable R F hF hFm Λ (DU).physicalState (DV).physicalState
    (DU).physicalField (DV).physicalField (DU).physicalState_measurable (DV).physicalState_measurable
    (DU).physicalField_measurable (DV).physicalField_measurable k

/-- ONE original sample event works for EVERY output terminal and
history. No fixed-terminal exceptional set is evaluated diagonally. -/
theorem point_initial_ae:
    ∀ᵐω ∂μ,∀T:Icc (0:ℝ) (h:ℝ),∀k:ℕ,∀p:History HeatCircle k,
      MixedPastTerminalEndpointWord.wordDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le (ZZ (⟨T,T.2.1⟩:ℝ≥0)) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
        F hF hFm k p ω=
      InitialTerminalFields.point R F hF hFm Λ (DU).physicalState (DV).physicalState
        (DU).physicalField (DV).physicalField k T p ω:=by
  filter_upwards [MixedNativeAdditiveResidualPair.first_zero 𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S,
    MixedNativeAdditiveResidualPair.second_zero 𝓕 μ H hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S] with ω hU hV
  intro T k p
  let TN:ℝ≥0:=⟨T,T.2.1⟩
  have hprof:(ControlledReferenceLevel.referenceData P P.coefficient haP Λ 1 0 TN bot_le (embed u₀,0)).reference=
      (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 TN bot_le (embed u₀,0)).reference:=by
    funext z
    simpa only [ControlledReferenceLevel.referenceData,ControlledReferenceWindows.coefficient,NNReal.coe_zero,sub_zero] using
      (ZeroDirectionProfile.profile P Λ 1 (embed u₀) (z.1,z.2)).trans
      (ZeroDirectionProfile.profile P Λ 0 (embed u₀) (z.1,z.2)).symm
  have ht:=WordRootReindex.test (K 0 TN) (K 1 TN) id rfl (fun _=>rfl) (fun _=>rfl)
    hprof rfl (fun _=>rfl) k p
  have hs:=WordRootReindex.strict_iff (K 0 TN) (Zero TN) id rfl (fun _=>rfl) k p
  have hn:=WordRootReindex.current (K 0 TN) (Zero TN) id rfl (fun _=>rfl) (fun _=>rfl)
    Λ (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField k p ω
  have ho:=WordRootReindex.current (K 0 TN) (Zero TN) id rfl (fun _=>rfl) (fun _=>rfl)
    Λ (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField k p ω
  have hi:∀k:ℕ,∀p:History HeatCircle k,WordRootReindex.history (id:HeatCircle→HeatCircle) k p=p:=by
    intro k
    induction k with
    | zero=>intro p;rfl
    | succ k ih=>intro p;exact congrArg (fun a=>(a,p.2)) (ih p.1)
  simp only [hi k p] at ht hs hn ho
  have hf:=InitialTerminalFibre.point R F hF hFm (K 0 TN) T rfl (fun _=>rfl) (fun _=>rfl)
    rfl rfl (fun _=>rfl) Λ (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField k p ω
  unfold MixedPastTerminalEndpointWord.wordDifference
  simp only [MixedPastJointData.pastU,MixedPastJointData.pastD,hU,hV,sub_self,map_zero]
  rw [hf]
  change (if PhysicalParentGeometry.StrictHistory (Zero TN) k p then _ else 0)=_
  rw [hs]
  split_ifs
  · rw [hU,hV]
    have hz:(embed (u₀-u₀):CircleL2)=0:=(map_sub embed u₀ u₀).trans (sub_self _)
    rw [hz,ht]
    dsimp only [MixedPastTerminalPairedFields.current,Bool.false_eq_true,if_false,if_true]
    rw [hn,ho]
    rfl
  · rfl

/-- Exact actual original-history value on ONE sample event for every
initial output time. The fixed ambient horizon has no omitted strip. -/
theorem value_initial_ae:
    ∀ᵐω ∂μ,∀T:Icc (0:ℝ) (h:ℝ),∀k:ℕ,
      (∫p:History HeatCircle k,MixedPastTerminalEndpointWord.wordDifference
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 (⟨T,T.2.1⟩:ℝ≥0) bot_le
        (ZZ (⟨T,T.2.1⟩:ℝ≥0)) (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k p ω
        ∂historyMeasure (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0
          (⟨T,T.2.1⟩:ℝ≥0) bot_le (0,0)) AddCircle.haarAddCircle k)=
      value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k T ω:=by
  filter_upwards [point_initial_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T k
  let TN:ℝ≥0:=⟨T,T.2.1⟩
  let Q:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 TN bot_le (0,0)
  let f:=fun p:History HeatCircle k=>MixedPastTerminalEndpointWord.wordDifference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 TN bot_le (ZZ TN)
      (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k p ω
  have he:(∫p,f p ∂historyMeasure Q AddCircle.haarAddCircle k)=∫p,f p ∂historyMeasure R AddCircle.haarAddCircle k:=by
    apply HistoryHorizonIntegration.integral_eq Q R rfl T.2.2 AddCircle.haarAddCircle k f
    intro p hp
    have hn:¬PhysicalParentGeometry.StrictHistory (Zero TN) k p:=by
      intro hs
      exact hp (HistoryHorizonIntegration.strict_mem (Zero TN) (TN:ℝ) (fun _=>le_rfl) k p hs)
    exact if_neg hn
  refine he.trans ?_
  apply integral_congr_ae
  exact ae_of_all _ (fun p=>hω T k p)

end SHE.InitialNativeWordFields
