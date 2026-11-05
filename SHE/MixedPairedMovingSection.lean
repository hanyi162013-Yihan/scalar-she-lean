module

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

namespace SHE.MixedPairedMovingSection
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedPairedMovingSection_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedPairedMovingSection_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedPairedMovingSection_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedPairedMovingSection_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPairedMovingSection_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedPairedMovingSection_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPairedMovingSection_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedPairedMovingSection_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPairedMovingSection_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPairedMovingSection_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedPairedMovingSection_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedPairedMovingSection_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

def value (v:ℝ≥0) (k:ℕ) (ν χ:ℝ) (ω:Ω):ℝ:=
  ∫hist,MixedPastTerminalPairedWord.point
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v (v+h) le_self_add
      (ZT v) (HT v) (HS v) F hF hFm k ν χ hist ω
    ∂historyMeasure (ControlledReferenceLevel.referenceData P P.coefficient haP Λ 0 v (v+h) le_self_add (0,0))
      AddCircle.haarAddCircle k

local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- The literal ORIGINAL-history paired remainder on a moving physical
window has the exact relative RMS/current-energy bound. Every stochastic,
Gaussian, old-history, and absolute-integrability input is discharged. -/
theorem actual_section_energy
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
    (v:ℝ≥0) (hvH:v+h≤H):
    let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))
    let A:=fun t=>RMS (k+1) t ν χ A0 order B0
    let E:=fun t=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      ((v:ℝ)+Clock (k+1) t).toNNReal
    Integrable (fun ω=>|Value v (k+1) ν χ ω|^2) μ ∧
      (∫ω,|Value v (k+1) ν χ ω|^2 ∂μ)≤
        2*(∫t,A t ∂η)*((∫t,A t*(E t)^χ ∂η)+
          (∫t,A t ∂η)*(MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v)^χ):=by
  intro η A E
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
  have ht:=MixedPastTerminalPairedHistoryEnergy.actual_history_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP v (v+h) le_self_add
    (ZT v) (HT v) (HS v) F hF hFm hlocal hΛ hH hvb hagesAbs hsAbs htAbs hcAbs hspanAbs hvH hsmallP
    k hsmallAbs hA0 hν hχ hχβ hjet order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov
  dsimp only at ht
  rw [MixedPairedClockIntegrals.mass_translation (Λ:=Λ) (κ:=κ) (M:=M) (P:=P) (haP:=haP)
      (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm) v (k+1) χ A0 ν order B0,
    MixedPairedClockIntegrals.energy_translation
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm v (k+1) χ A0 ν order B0] at ht
  constructor
  · convert! ht.2.1 using 1
  · convert! ht.2.2 using 1

end SHE.MixedPairedMovingSection

