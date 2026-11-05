module

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

namespace SHE.MovingPairedFields
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingPairedFields_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingPairedFields_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingPairedFields_instance3 : MeasurableSpace RealL2 := borel _
local instance movingPairedFields_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingPairedFields_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingPairedFields_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingPairedFields_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingPairedFields_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingPairedFields_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingPairedFields_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingPairedFields_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingPairedFields_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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
open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm (0,(0,0))
local notation "Abs"=>fun v=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v
local notation "DataU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DataV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "RC"=>RelativePairedCurrent.current P haP Λ h Z htarget hstop F hF hFm
local notation "Value"=>MixedPairedMovingSection.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

/-- The literal paired field transported to a FIXED original relative
history measure. Both endpoint current states are actual physical fields. -/
def relativePoint (k:ℕ) (ν χ:ℝ) (v:ℝ) (hist:History HeatCircle k) (ω:Ω):ℝ:=
  if PhysicalParentGeometry.StrictHistory Rel k hist then
    ControlledFiniteEndpointComparison.paired P haP Λ 0 h bot_le Z htarget hstop F hF hFm
      (embed (S.first v.toNNReal ω),embed (S.second v.toNNReal ω-S.first v.toNNReal ω)) k hist
      (RC (DataU).physicalState (DataV).physicalState (DataU).physicalField (DataV).physicalField k v hist ω)
      (RC (DataU).physicalState (DataU).physicalState (DataU).physicalField (DataU).physicalField k v hist ω) ν χ
  else 0
local notation "RP"=>relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem relativePoint_measurable (k:ℕ) (ν χ:ℝ):
    Measurable (fun z:ℝ×(History HeatCircle k×Ω)=>RP k ν χ z.1 z.2.1 z.2.2):=by
  have hp:Measurable (fun z:ℝ×(History HeatCircle k×Ω)=>
      (embed (S.first z.1.toNNReal z.2.2),embed (S.second z.1.toNNReal z.2.2-S.first z.1.toNNReal z.2.2))):=
    (MovingNativeFields.past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S).comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd.snd)
  have hn:=RelativePairedCurrent.current_measurable P haP Λ h Z htarget hstop F hF hFm
    (DataU).physicalState (DataV).physicalState (DataU).physicalField (DataV).physicalField
    (DataU).physicalState_measurable (DataV).physicalState_measurable
    (DataU).physicalField_measurable (DataV).physicalField_measurable k
  have ho:=RelativePairedCurrent.current_measurable P haP Λ h Z htarget hstop F hF hFm
    (DataU).physicalState (DataU).physicalState (DataU).physicalField (DataU).physicalField
    (DataU).physicalState_measurable (DataU).physicalState_measurable
    (DataU).physicalField_measurable (DataU).physicalField_measurable k
  have hm:=PairedFamilyFields.paired_variable_measurable P haP Λ 0 h bot_le Z htarget hstop F hF hFm
    k _ hp (fun z:ℝ×(History HeatCircle k×Ω)=>z.2.1) measurable_snd.fst _ _ hn ho ν χ
  exact hm.ite ((PhysicalParentGeometry.strictHistory_measurableSet Rel k).preimage measurable_snd.fst) measurable_const

theorem point_translation (v:ℝ≥0) (k:ℕ) (ν χ:ℝ) (hist:History HeatCircle k) (ω:Ω):
    MixedPastTerminalPairedWord.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm k ν χ (ShiftedWordGeometry.shift (v:ℝ) k hist) ω=
      RP k ν χ v hist ω:=by
  let K:=Abs v
  have hb:=ControlledWordTimeShift.base_shift P P.coefficient haP Λ h v (0,(0,0))
  have ht:=ControlledWordTimeShift.terminal_shift P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
  have hs:=PairedTimeTranslation.strict_shift Rel K (v:ℝ) hb ht k hist
  have hc(second:Bool):MixedPastTerminalPairedFields.current 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm second k
        (ShiftedWordGeometry.shift (v:ℝ) k hist) ω=
      if second then RC (DataU).physicalState (DataV).physicalState (DataU).physicalField (DataV).physicalField k v hist ω
      else RC (DataU).physicalState (DataU).physicalState (DataU).physicalField (DataU).physicalField k v hist ω:=by
    cases second
    · exact RelativePairedCurrent.current_translation P haP Λ h Z htarget hstop F hF hFm
        (DataU).physicalState (DataU).physicalState (DataU).physicalField (DataU).physicalField v k hist ω
    · exact RelativePairedCurrent.current_translation P haP Λ h Z htarget hstop F hF hFm
        (DataU).physicalState (DataV).physicalState (DataU).physicalField (DataV).physicalField v k hist ω
  unfold MixedPastTerminalPairedWord.point relativePoint
  rw [hs]
  simp only [Real.toNNReal_coe]
  split_ifs with hstrict
  · rw [hc true,hc false]
    exact ControlledPairedClockShift.paired_translation P haP Λ h Z htarget hstop F hF hFm v
      (embed (S.first v ω),embed (S.second v ω-S.first v ω)) k hist _ _ ν χ
  · rfl

theorem value_relative (v:ℝ≥0) (k:ℕ) (ν χ:ℝ) (ω:Ω):
    Value v k ν χ ω=
      ∫hist,RP k ν χ v hist ω ∂historyMeasure
        (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (0,0)) AddCircle.haarAddCircle k:=by
  let R:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (0,0)
  let Q:=ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v (v+h) le_self_add (0,0)
  have hb:Q.base=R.base+(v:ℝ):=by change (v:ℝ)=0+(v:ℝ);ring
  have hh:Q.horizon=R.horizon+(v:ℝ):=by change ((v+h:ℝ≥0):ℝ)=(h:ℝ)+(v:ℝ);simp only [NNReal.coe_add,add_comm]
  rw [MixedPairedMovingSection.value,←ShiftedHistoryMeasure.integral_translation R Q (v:ℝ) hb hh AddCircle.haarAddCircle k]
  apply integral_congr_ae
  filter_upwards with hist
  exact point_translation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm v k ν χ hist ω

/-- Genuine moving-past/sample Borel measurability of the ORIGINAL
history average, obtained by exact transport to a fixed history measure. -/
theorem value_measurable (k:ℕ) (ν χ:ℝ):
    Measurable (fun z:ℝ≥0×Ω=>Value z.1 k ν χ z.2):=by
  have hm:Measurable (fun z:(ℝ≥0×Ω)×History HeatCircle k=>RP k ν χ z.1.1 z.2 z.1.2):=
    (relativePoint_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k ν χ).comp
      ((measurable_subtype_coe.comp measurable_fst.fst).prodMk (measurable_snd.prodMk measurable_fst.snd))
  have hi:=hm.stronglyMeasurable.integral_prod_right' (ν:=historyMeasure
    (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 h bot_le (0,0)) AddCircle.haarAddCircle k)
  convert! hi.measurable using 1
  funext z
  exact value_relative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm z.1 k ν χ z.2

end SHE.MovingPairedFields
