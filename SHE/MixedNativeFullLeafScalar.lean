module

public import SHE.MixedNativePairedLeafAverage
public import SHE.RootSectionRelativeIdentity
public import SHE.FullNativeRemainderIdentity
public import SHE.FullNativeRemainderEnergy
public import SHE.InitialOutputExtension
public import SHE.InitialCompleteTimePatch
public import SHE.InitialRetainedFrequencyEnergy
public import SHE.RetainedTerminalAllFrequency
public import SHE.PairedBudgetFrequency
public import SHE.FrequencyTimeInflation
public import SHE.InitialNativeSpatialFields
public import SHE.InitialRetainedSectionEnergy
public import SHE.InitialNativeClock
public import SHE.InitialActualConvolution
public import SHE.MixedTerminalEnergySplit
public import SHE.InitialActualRMSEnvelope
public import SHE.InitialRMSGapEnvelope
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

namespace SHE.MixedNativeFullLeafScalar
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance fullNativeRemainderIdentity_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance fullNativeRemainderIdentity_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance fullNativeRemainderIdentity_instance3 : MeasurableSpace RealL2 := borel _
local instance fullNativeRemainderIdentity_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullNativeRemainderIdentity_instance5 : MeasurableSpace CircleL2 := borel _
local instance fullNativeRemainderIdentity_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullNativeRemainderIdentity_instance7 : MeasurableSpace RealHaarInput := borel _
local instance fullNativeRemainderIdentity_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullNativeRemainderIdentity_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullNativeRemainderIdentity_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance fullNativeRemainderIdentity_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance fullNativeRemainderIdentity_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "RT" T:max=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=0) (b:=T) (hvb:=bot_le) (Z:=ZZ T) (htarget:=fun _ _=>le_rfl) (hstop:=fun _ _=>le_rfl)
  (F:=F) (hF:=hF) (hFm:=hFm)
local notation "En" T:max=>MixedPastTerminalTimeFields.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 T bot_le (ZZ T)
    (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm

local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S


local notation "Field"=>FullNativeRemainderEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) (ZZ h)
local notation "HT" v:max=>ControlledWordTimeShift.translatedTargets h (ZZ h) (fun _ _=>le_rfl) v
local notation "HS" v:max=>ControlledWordTimeShift.translatedStops h (ZZ h) (fun _ _=>le_rfl) v

def stop(v:ℝ≥0)(x:HeatCircle):((ZT v).observations x 0).stop=((v+h):ℝ):=by
  change (h:ℝ)+(v:ℝ)=(v:ℝ)+(h:ℝ)
  exact add_comm _ _

def target(v:ℝ≥0)(x:HeatCircle):((ZT v).observations x 0).target=((v+h):ℝ):=by
  change (h:ℝ)+(v:ℝ)=(v:ℝ)+(h:ℝ)
  exact add_comm _ _

def initial(T:ℝ≥0)(k:ℕ)(z:Ω×HeatCircle):ℝ:=
  MixedNativePairedLeafAverage.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP 0 T bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm k z
local notation "Initial"=>initial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP F hF hFm

def complete(v:ℝ≥0)(k:ℕ)(z:Ω×HeatCircle):ℝ:=
  MixedNativePairedLeafAverage.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add (ZT v)
    (stop h v) (target h v) F hF hFm k z
local notation "Complete"=>complete 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm

/-- The already estimated genuine initial-triangle remainder is exactly
the paired scalar field attached to the finite Hilbert expansion, on ONE
sample event for every terminal time, order and output root. -/
theorem initial_ae:
    ∀ᵐω∂μ,∀T:ℝ≥0,0<T→T≤h→∀k:ℕ,∀x:HeatCircle,
      Field k (T,(ω,x))=Initial T k (ω,x):=by
  filter_upwards [FullNativeRemainderIdentity.initial_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T hT hTh k x
  rw [hω T hT hTh k x]
  change HistoryProductMeasure.rootAverage
      (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 0 T bot_le (0,0)) k
      (fun a=>MixedPastTerminalEndpointWord.wordDifference
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP 0 T bot_le (ZZ T)
          (fun _ _=>le_rfl) (fun _ _=>le_rfl) F hF hFm k a.2 a.1) (ω,x)=_
  exact RootSectionRelativeIdentity.eq _ _ _ _

/-- The completed-window original terminal remainder is the SAME paired
field, after translating every old spatial coordinate before averaging. -/
theorem complete_eq(v:ℝ≥0)(hv:0<v)(hvH:v+h≤H)(k:ℕ)(z:Ω×HeatCircle):
    Field k (((v+h:ℝ≥0):ℝ),z)=Complete v k z:=by
  rw [FullNativeRemainderIdentity.complete_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm v hv hvH k z]
  change HistoryProductMeasure.rootAverage
      (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v (v+h) le_self_add (0,0)) k
      (fun a=>MixedPastTerminalEndpointWord.wordDifference
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v (v+h) le_self_add
          (ZT v) (HT v) (HS v) F hF hFm k a.2 a.1) z=_
  exact RootSectionRelativeIdentity.eq _ _ _ _
end SHE.MixedNativeFullLeafScalar
