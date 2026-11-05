module

public import SHE.RetainedTerminalEnergySplit
public import SHE.RetainedPairedMovingSection
public import SHE.MovingTerminalSpatialFields
public import SHE.MovingTerminalWordFields
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

namespace SHE.RetainedMovingEnergySection
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingTerminalEnergySection_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingTerminalEnergySection_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingTerminalEnergySection_instance3 : MeasurableSpace RealL2 := borel _
local instance movingTerminalEnergySection_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingTerminalEnergySection_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingTerminalEnergySection_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingTerminalEnergySection_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingTerminalEnergySection_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingTerminalEnergySection_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingTerminalEnergySection_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingTerminalEnergySection_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingTerminalEnergySection_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

local notation "WordValue"=>MovingTerminalSpatialFields.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "PairValue"=>RetainedPairedMovingSection.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
theorem actual_section_split
    (hlocal:StandardTerminalPastLocality J) (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hh:0<h)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootstop:∀x i,(Z.observations x i).stop=(h:ℝ))
    (hrootage:∀x i,(Z.observations x i).target=(h:ℝ))
    (hcenter:∀x i,(Z.observations x i).center=x)
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
    (v:ℝ≥0) (hvH:v+h≤H) :
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let B:=QuarterRMSTimeFactors.oldTimeBudget P (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) h 0 1 A0 ν
    let Epast:=MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
    Integrable (fun ω=>|WordValue v (k+1) ω|^2) (μ.prod AddCircle.haarAddCircle) ∧
      Integrable (fun ω=>|PairValue v (k+1) ν χ ω|^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫ω,|WordValue v (k+1) ω|^2 ∂μ.prod AddCircle.haarAddCircle)≤
        2*((CC*Cm^2*(Fintype.card (OrderedHeatForests.Choices 1 (k+1)):ℝ)^2)*(B/2)^2*Epast^P.exponent+
          (∫ω,|PairValue v (k+1) ν χ ω|^2 ∂μ.prod AddCircle.haarAddCircle)):=by
  intro CC Cm B Epast
  have hvb:v<v+h:=lt_add_of_pos_right v hh
  have hspanAbs:((v+h:ℝ≥0):ℝ)-(v:ℝ)≤P.horizon:=by simpa only [NNReal.coe_add,add_sub_cancel_left] using hspan
  have hsmallAbs:∀j,j<k+1→((v+h:ℝ≥0):ℝ)-(v:ℝ)≤PhysicalScoreChain.uniformHorizon 1 j:=by
    simpa only [NNReal.coe_add,add_sub_cancel_left] using hsmall
  have hagesAbs:∀x i,((ZT v).observations x i).stop≤((ZT v).observations x i).target:=by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤(Z.observations x i).target+(v:ℝ)
    linarith [hages x i]
  have hsAbs:∀x i,((ZT v).observations x i).stop=((v+h:ℝ≥0):ℝ):=by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)=_
    rw [hrootstop x i,NNReal.coe_add,add_comm]
  have htAbs:∀x i,((ZT v).observations x i).target=((v+h:ℝ≥0):ℝ):=by
    intro x i
    change (Z.observations x i).target+(v:ℝ)=_
    rw [hrootage x i,NNReal.coe_add,add_comm]
  have hcAbs:∀x i,((ZT v).observations x i).center=x:=hcenter
  have ht:=RetainedTerminalEnergySplit.actual_spatial_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm hlocal hΛ hH hvb hagesAbs hsAbs htAbs hcAbs hspanAbs hvH hsmallP
    k hsmallAbs hA0 hν hχ hχβ hjet order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  dsimp only at ht
  simp only [NNReal.coe_add,add_sub_cancel_left] at ht
  simp only [MovingTerminalSpatialFields.value_absolute]
  convert! ht.2 using 1

end SHE.RetainedMovingEnergySection
