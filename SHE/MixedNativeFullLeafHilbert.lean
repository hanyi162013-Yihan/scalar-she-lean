module

public import SHE.MixedNativeFullLeafScalar
public import SHE.MixedNativePairedLeafHilbert
public import SHE.NativeBesselSectionEnergy
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

namespace SHE.MixedNativeFullLeafHilbert
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



local notation "Scalar"=>FullNativeRemainderEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm
local notation "ZT" v:max=>ObservationFamilyTimeShift.family (v:ℝ) (ZZ h)
local notation "Stop"=>MixedNativeFullLeafScalar.stop h
local notation "Target"=>MixedNativeFullLeafScalar.target h
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)

def field(k:ℕ)(z:ℝ×Ω):CircleL2:=
  NativeBesselFieldAE.value Λ ρ hL hρ
    (fun a:(ℝ×Ω)×HeatCircle=>(Scalar k (a.1.1,(a.1.2,a.2)):ℂ)) z
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ

theorem scalar_measurable(k:ℕ):Measurable
    (fun a:(ℝ×Ω)×HeatCircle=>(Scalar k (a.1.1,(a.1.2,a.2)):ℂ)):=
  Complex.continuous_ofReal.measurable.comp ((FullNativeRemainderEnergy.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))

theorem field_measurable(k:ℕ):Measurable (Field k):=
  NativeBesselFieldAE.measurable Λ ρ hL hρ _ (scalar_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k)

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "InitialLeaf" T:max=>MixedNativePairedHilbertExpansion.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 T bot_le
  (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm hL hρ
local notation "CompleteLeaf" v:max=>MixedNativePairedHilbertExpansion.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs v (v+h) le_self_add
  (ZT v) (Stop v) (Target v) F hF hFm hL hρ

include hsmall in
/-- One sample event identifies the full initial-strip native remainder
with the exact finite-expansion terminal leaf, simultaneously at every
terminal time and every finite order. -/
theorem initial_ae(hA:P.coefficient=(fun z=>κ+aV z)):
    ∀ᵐω∂μ,∀T:ℝ≥0,0<T→T≤h→∀k:ℕ,Field k (T,ω)= (InitialLeaf T) k ω:=by
  filter_upwards [MixedNativeFullLeafScalar.initial_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm] with ω hω
  intro T hT hTh k
  let Y:Ω×HeatCircle→ℝ:=fun z=>Scalar k (T,z)
  have hY:Measurable Y:=(FullNativeRemainderEnergy.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp
    (measurable_const.prodMk measurable_id)
  change NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Y z:ℂ)) ω=_
  exact MixedNativePairedLeafHilbert.native_eq_of_section
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs 0 T bot_le (ZZ T) (fun _=>rfl) (fun _=>rfl) F hF hFm
    hsmall hL hρ hA Y hY k ω (ae_of_all _ (fun x=>hω T hT hTh k x))

include hsmall in
/-- Every completed-window native terminal leaf is exactly the same
Borel full-time remainder used in the actual energy estimate. -/
theorem complete_eq(hA:P.coefficient=(fun z=>κ+aV z))(v:ℝ≥0)(hv:0<v)(hvH:v+h≤H)(k:ℕ)(ω:Ω):
    Field k (((v+h:ℝ≥0):ℝ),ω)= (CompleteLeaf v) k ω:=by
  let Y:Ω×HeatCircle→ℝ:=fun z=>Scalar k (((v+h:ℝ≥0):ℝ),z)
  have hY:Measurable Y:=(FullNativeRemainderEnergy.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm k).comp
    (measurable_const.prodMk measurable_id)
  change NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Y z:ℂ)) ω=_
  exact MixedNativePairedLeafHilbert.native_eq_of_section
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v (v+h) le_self_add (ZT v) (Stop v) (Target v) F hF hFm
    hsmall hL hρ hA Y hY k ω (ae_of_all _ (fun x=>
      MixedNativeFullLeafScalar.complete_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm v hv hvH k (ω,x)))
end SHE.MixedNativeFullLeafHilbert
