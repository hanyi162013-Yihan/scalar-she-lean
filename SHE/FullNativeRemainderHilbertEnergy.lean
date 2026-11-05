module

public import SHE.FullNativeRemainderEnergy
public import SHE.MixedNativeFullLeafHilbert
public import SHE.NativeBesselSectionEnergy
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

namespace SHE.FullNativeRemainderHilbertEnergy
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance fullNativeRemainderEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance fullNativeRemainderEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance fullNativeRemainderEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance fullNativeRemainderEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance fullNativeRemainderEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance fullNativeRemainderEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance fullNativeRemainderEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance fullNativeRemainderEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance fullNativeRemainderEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
local notation "Native"=>MixedNativeFullLeafHilbert.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm hL hρ

include hIJ₀ hIJ₁ in
/-- The literal full native remainder has the actual all-output-time
energy cap with the sharp massive Bessel factor. Initial triangles,
original old-history measures and finite derivative order are retained. -/
theorem actual_frequency_energy
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hh:0<h) (hhH:h≤H)
    (hspan:(h:ℝ)≤P.horizon)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov)
    {η:ℝ} (hη:0<η):
    let Cp:=PairedBudgetFrequency.constant P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) χ η order B0
    let Cc:=TerminalCovarianceBudget.constant P (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) η
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let base:=CC*Cm^2*(Fintype.card (OrderedHeatForests.Choices 1 (k+1)):ℝ)^2
    let cap:=max 1 (MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M*(H:ℝ))
    let C:=2*base*(Cc/2)^2*cap^(P.exponent-χ)*(H:ℝ)^(1-P.exponent)+12*Cp^2*(H:ℝ)^(1-χ)
    let νT:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    Integrable (fun z:ℝ×Ω=>‖Native (k+1) z‖^2) (νT.prod μ) ∧
      (∫z:ℝ×Ω,‖Native (k+1) z‖^2 ∂νT.prod μ)≤
        Λ^(-ρ)*(C*A0^2*(1+ν)^(2*(χ+η))*(h:ℝ)^((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2)*Mglobal^χ) :=by
  intro Cp Cc CC Cm base cap C νT
  let Ecap:=C*A0^2*(1+ν)^(2*(χ+η))*(h:ℝ)^((((k+1:ℕ):ℝ)*P.exponent-χ-η)/2)*Mglobal^χ
  have hs:=FullNativeRemainderEnergy.actual_frequency_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm J hIJ₀ hIJ₁
    hlocal hΛ hH hh hhH hspan hsmallP k hsmall hA0 hν hχ hχβ hjet
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hη
  change Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Scalar (k+1) z|^2)
      (νT.prod (μ.prod AddCircle.haarAddCircle)) ∧
      (∫z:ℝ×(Ω×HeatCircle),|Scalar (k+1) z|^2 ∂νT.prod (μ.prod AddCircle.haarAddCircle))≤Ecap at hs
  let B:((ℝ×Ω)×HeatCircle)→ℂ:=fun z=>(Scalar (k+1) (z.1.1,(z.1.2,z.2)):ℂ)
  have hB:Measurable B:=MixedNativeFullLeafHilbert.scalar_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h F hF hFm (k+1)
  have hp:=measurePreserving_prodAssoc νT μ (AddCircle.haarAddCircle:Measure HeatCircle)
  have hAssoc_apply(z:(ℝ×Ω)×HeatCircle):
      (MeasurableEquiv.prodAssoc z:ℝ×(Ω×HeatCircle))=(z.1.1,(z.1.2,z.2)):=rfl
  have hiB:Integrable (fun z=>‖B z‖^2) ((νT.prod μ).prod AddCircle.haarAddCircle):=by
    have hx:=(hp.integrable_comp hs.1.aestronglyMeasurable).mpr hs.1
    simpa only [Function.comp_def,B,Complex.norm_real,Real.norm_eq_abs,hAssoc_apply] using hx
  have he:(∫z,‖B z‖^2 ∂(νT.prod μ).prod AddCircle.haarAddCircle)=
      ∫z:ℝ×(Ω×HeatCircle),|Scalar (k+1) z|^2 ∂νT.prod (μ.prod AddCircle.haarAddCircle):=by
    simpa only [B,Complex.norm_real,Real.norm_eq_abs,hAssoc_apply] using
      hp.integral_comp' (fun z:ℝ×(Ω×HeatCircle)=>|Scalar (k+1) z|^2)
  have hcap:(∫z,‖B z‖^2 ∂(νT.prod μ).prod AddCircle.haarAddCircle)≤Ecap:=he.trans_le hs.2
  exact NativeBesselSectionEnergy.energy_of_integral_bound Λ ρ hL hρ (νT.prod μ) B hB hiB Ecap hcap
end SHE.FullNativeRemainderHilbertEnergy
