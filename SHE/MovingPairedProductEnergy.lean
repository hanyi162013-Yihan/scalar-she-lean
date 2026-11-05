module

public import SHE.MovingPairedBandEnergy
public import SHE.MovingPairedFields
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

namespace SHE.MovingPairedProductEnergy
open Classical
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingPairedProductEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingPairedProductEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingPairedProductEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance movingPairedProductEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingPairedProductEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingPairedProductEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingPairedProductEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingPairedProductEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingPairedProductEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingPairedProductEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingPairedProductEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingPairedProductEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

local notation "Field"=>MovingPairedRemainderEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

/-- The literal moving-past paired remainder is jointly Borel in
physical past time and sample, including the physical-window guard. -/
theorem field_measurable (k:ℕ) (ν χ:ℝ):
    Measurable (fun z:ℝ×Ω=>Field k ν χ z.1 z.2):=by
  classical
  have hmap:Measurable (fun z:ℝ×Ω=>(z.1.toNNReal,z.2)):=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  have hm:Measurable (fun z:ℝ×Ω=>Value z.1.toNNReal k ν χ z.2):=by
    convert! (MovingPairedFields.value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k ν χ).comp hmap using 1
  have hset:MeasurableSet {z:ℝ×Ω | 0≤z.1 ∧ z.1+(h:ℝ)≤(H:ℝ)}:=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le (measurable_fst.add_const (h:ℝ)) measurable_const)
  have hi:Measurable (fun z:ℝ×Ω=>if 0≤z.1 ∧ z.1+(h:ℝ)≤(H:ℝ) then
      Value z.1.toNNReal k ν χ z.2 else (0:ℝ)):=hm.ite hset measurable_const
  simpa only [MovingPairedRemainderEnergy.field] using hi

include hIJ₀ hIJ₁ in
theorem actual_product_band_energy
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
    (hhH:h≤H) {η:ℝ} (hη:0<η) (hband:(1+ν)^(-4:ℝ)≤(h:ℝ)):
    let C:=PairedBudgetFrequency.constant P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) χ η order B0
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    Integrable (fun z:ℝ×Ω=>|Field (k+1) ν χ z.1 z.2|^2) (νv.prod μ) ∧
      (∫z:ℝ×Ω,|Field (k+1) ν χ z.1 z.2|^2 ∂νv.prod μ)≤
      4*(A0*C*(1+ν)^(χ+η)*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/4))^2*
        Mglobal^χ*(H:ℝ)^(1-χ):=by
  intro C νv
  let bound:=4*(A0*C*(1+ν)^(χ+η)*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/4))^2*
    Mglobal^χ*(H:ℝ)^(1-χ)
  have hb:=MovingPairedBandEnergy.actual_global_band_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h Z htarget hstop F hF hFm
    hlocal hΛ hH hh hages hrootstop hrootage hcenter hspan hsmallP k hsmall hA0 hν hχ hχβ hjet
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hhH hη hband
  have hm:Measurable (fun z:ℝ×Ω=>|Field (k+1) ν χ z.1 z.2|^2):=
    (continuous_abs.measurable.comp (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm (k+1) ν χ)).pow_const 2
  have ht:(∫⁻z:ℝ×Ω,ENNReal.ofReal (|Field (k+1) ν χ z.1 z.2|^2) ∂νv.prod μ)≤ENNReal.ofReal bound:=by
    calc
      _=(∫⁻v, (∫⁻ω,ENNReal.ofReal (|Field (k+1) ν χ v ω|^2) ∂μ) ∂νv):=by
        apply lintegral_prod (μ:=νv) (ν:=μ)
        convert! (ENNReal.measurable_ofReal.comp hm).aemeasurable using 1
      _≤_:=hb
  have hi:Integrable (fun z:ℝ×Ω=>|Field (k+1) ν χ z.1 z.2|^2) (νv.prod μ):=by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
    exact ht.trans_lt ENNReal.ofReal_lt_top
  have hbound:0≤bound:=by
    dsimp only [bound]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (Real.rpow_nonneg (MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) _))
      (Real.rpow_nonneg H.2 _)
  refine ⟨hi,(ENNReal.ofReal_le_ofReal_iff hbound).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))]
  exact ht

end SHE.MovingPairedProductEnergy
