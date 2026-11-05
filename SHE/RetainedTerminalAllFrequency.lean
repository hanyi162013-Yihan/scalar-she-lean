module

public import SHE.FrequencyTimeInflation
public import SHE.RetainedTerminalFrequencyEnergy
public import SHE.TerminalCovarianceSquared
public import SHE.MixedGlobalEnergyPower
public import SHE.RetainedMovingRemainderEnergy
public import SHE.RetainedMovingEnergySection
public import SHE.MovingTerminalSpatialFields
public import SHE.MovingPairedProductEnergy
public import SHE.PairedBudgetFrequency
public import SHE.MovingPairedRemainderEnergy
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.MixedPairedMovingSection
public import SHE.MixedPairedMovingKernel
public import SHE.MovingPairedRMSBudget
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

namespace SHE.RetainedTerminalAllFrequency
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingTerminalAllFrequency_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingTerminalAllFrequency_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingTerminalAllFrequency_instance3 : MeasurableSpace RealL2 := borel _
local instance movingTerminalAllFrequency_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingTerminalAllFrequency_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingTerminalAllFrequency_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingTerminalAllFrequency_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingTerminalAllFrequency_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingTerminalAllFrequency_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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
local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

open CutoffWordHistories CutoffCarriers ControlledProfile SmoothCylinders UniformSmooth
variable (P:CanonicalCovariance.ProfileParameters) (haP:BoundedSmooth P.coefficient)
variable (h:ℝ≥0) (Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Rel"=>ControlledWordTimeShift.relativeLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm (0,(0,0))
local notation "RMS"=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=0) (b:=h) (hvb:=bot_le) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)

local notation "Abs" v=>ControlledWordTimeShift.absoluteLevel P P.coefficient haP Λ h Z htarget hstop F hF hFm v (0,(0,0))
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v

local notation "RAbs" v=>MixedPastTerminalRMS.amplitude (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP)
  (v:=v) (b:=v+h) (hvb:=le_self_add) (Z:=ZT v) (htarget:=HT v) (hstop:=HS v) (F:=F) (hF:=hF) (hFm:=hFm)
local notation "EAbs" v=>MixedPastTerminalTimeFields.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v (v+h) le_self_add (ZT v) (HT v) (HS v) F hF hFm
local notation "Clock"=>MixedPairedCurrentClock.clock (Λ:=Λ) (P:=P) (haP:=haP) (h:=h)
  (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)

local notation "Value"=>MixedPairedMovingSection.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "PairField"=>MovingPairedRemainderEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "WordValue"=>MovingTerminalSpatialFields.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Field"=>RetainedMovingRemainderEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- All-frequency actual finite-depth remainder. Auxiliary jet inflation
removes the native-band restriction on the SAME original recursive word.
Only an explicit quarter-age loss is paid in RMS; every original rough
gain and the true coupled global energy remain. -/
theorem actual_frequency_energy
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hh:0<h)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(h:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(h:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x) (hspan:(h:ℝ)≤P.horizon)
    (hsmallP:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k:ℕ) (hsmall:∀j,j<k+1→(h:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0<χ) (hχβ:χ<P.exponent)
    (hjet:∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (order:ℕ) (horder:0<order) (ho0:1≤(order:ℝ)*(1-χ))
    (ho1:1≤(order:ℝ)*(1-χ/P.exponent)) (B0 B1 Bcov:ℝ≥0)
    (hBDG:StandardTerminalBDGPower (order*((k+1)+2)) J B0)
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov)
    (hhH:h≤H) {η:ℝ} (hη:0<η) :
    let Cp:=PairedBudgetFrequency.constant P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) χ η order B0
    let Cc:=TerminalCovarianceBudget.constant P (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) η
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let base:=CC*Cm^2*(Fintype.card (OrderedHeatForests.Choices 1 (k+1)):ℝ)^2
    let cap:=max 1 (MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M*(H:ℝ))
    let C:=2*base*(Cc/2)^2*cap^(P.exponent-χ)*(H:ℝ)^(1-P.exponent)+8*Cp^2*(H:ℝ)^(1-χ)
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2) (νv.prod (μ.prod AddCircle.haarAddCircle)) ∧
      (∫z:ℝ×(Ω×HeatCircle),|Field (k+1) z.1 z.2|^2 ∂νv.prod (μ.prod AddCircle.haarAddCircle))≤
        C*A0^2*(1+ν)^(2*(χ+η))*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/2-(χ+η)/2)*Mglobal^χ :=by
  intro Cp Cc CC Cm base cap C νv
  let ν':=FrequencyTimeInflation.inflate (h:ℝ) ν
  have hνν':ν≤ν':=FrequencyTimeInflation.le_inflate (show 0<(h:ℝ) from hh)
    ((show (h:ℝ)≤(H:ℝ) from hhH).trans hH) hν
  have hν':0≤ν':=hν.trans hνν'
  have hj':∀x j,j≤k+2→∀z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν'^j:=by
    intro x j hj z
    exact (hjet x j hj z).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν hνν' j) hA0)
  have hb:=FrequencyTimeInflation.native_band (show 0<(h:ℝ) from hh) hν
  have he:=RetainedTerminalFrequencyEnergy.actual_frequency_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h Z htarget hstop F hF hFm
    hlocal hΛ hH hh hages hrootstop hrootage hcenter hspan hsmallP k hsmall hA0 hν' hχ hχβ hj'
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hhH hη hb
  have hraw:(∫z:ℝ×(Ω×HeatCircle),|Field (k+1) z.1 z.2|^2 ∂νv.prod (μ.prod AddCircle.haarAddCircle))≤
      C*A0^2*(1+ν')^(2*(χ+η))*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/2)*Mglobal^χ:=by
    convert! he.2 using 1
  refine ⟨he.1,hraw.trans_eq ?_⟩
  have hw:=FrequencyTimeInflation.weight_identity (show 0<(h:ℝ) from hh) hν
    (χ+η) (((k+1:ℕ):ℝ)*P.exponent/2)
  have hm:=congrArg (fun r:ℝ=>C*A0^2*r*Mglobal^χ) hw
  convert! hm using 1 <;> ring

end SHE.RetainedTerminalAllFrequency
