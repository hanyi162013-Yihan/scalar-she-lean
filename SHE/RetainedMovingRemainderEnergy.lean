module

public import SHE.RetainedMovingEnergySection
public import SHE.MovingTerminalSpatialFields
public import SHE.RetainedPairedProductEnergy
public import SHE.PairedBudgetFrequency
public import SHE.RetainedPairedMovingEnergy
public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.RetainedPairedMovingSection
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

namespace SHE.RetainedMovingRemainderEnergy
open Classical AddCircle
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingTerminalRemainderEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingTerminalRemainderEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingTerminalRemainderEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance movingTerminalRemainderEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingTerminalRemainderEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingTerminalRemainderEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingTerminalRemainderEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingTerminalRemainderEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingTerminalRemainderEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingTerminalRemainderEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingTerminalRemainderEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingTerminalRemainderEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

local notation "Value"=>RetainedPairedMovingSection.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "PairField"=>RetainedPairedMovingEnergy.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "WordValue"=>MovingTerminalSpatialFields.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

def field (k:ℕ) (v:ℝ) (ω:Ω×HeatCircle):ℝ:=
  if 0≤v ∧ v+(h:ℝ)≤(H:ℝ) then WordValue v.toNNReal k ω else 0
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem field_measurable (k:ℕ):Measurable (fun z:ℝ×(Ω×HeatCircle)=>Field k z.1 z.2):=by
  classical
  have hmap:Measurable (fun z:ℝ×(Ω×HeatCircle)=>(z.1.toNNReal,z.2)):=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  have hm:Measurable (fun z:ℝ×(Ω×HeatCircle)=>WordValue z.1.toNNReal k z.2):=by
    convert! (MovingTerminalSpatialFields.value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k).comp hmap using 1
  have hset:MeasurableSet {z:ℝ×(Ω×HeatCircle) | 0≤z.1 ∧ z.1+(h:ℝ)≤(H:ℝ)}:=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le (measurable_fst.add_const (h:ℝ)) measurable_const)
  have hi:Measurable (fun z:ℝ×(Ω×HeatCircle)=>if 0≤z.1 ∧ z.1+(h:ℝ)≤(H:ℝ) then
      WordValue z.1.toNNReal k z.2 else (0:ℝ)):=hm.ite hset measurable_const
  simpa only [field] using hi

include hIJ₀ hIJ₁ in
/-- COMPLETE actual finite recursive-word remainder on moving past
windows. Covariance and all paired current/own-baseline sources are
included. The original history average is square integrable on the
actual past/sample product, with the true global energy powers. -/
theorem actual_global_product_energy
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
    let PairBand:=A0*C*(1+ν)^(χ+η)*(h:ℝ)^(((k+1:ℕ):ℝ)*P.exponent/4)
    let CC:=MixedPastWordMoments.momentConstant P (k+1) (k+1) 1
      (((k+1:ℕ):ℝ)*(NativeHybridMoments.momentConstant (k+3) Bcov κ M)^P.exponent)
    let Cm:=2*P.holder*(3*(((1+k:ℕ):ℝ)/(P.lower/2)))
    let CovBudget:=QuarterRMSTimeFactors.oldTimeBudget P (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) h 0 1 A0 ν
    let Kcov:=(CC*Cm^2*(Fintype.card (OrderedHeatForests.Choices 1 (k+1)):ℝ)^2)*(CovBudget/2)^2
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2) (νv.prod (μ.prod haarAddCircle)) ∧
      (∫z:ℝ×(Ω×HeatCircle),|Field (k+1) z.1 z.2|^2 ∂νv.prod (μ.prod haarAddCircle))≤
        2*Kcov*Mglobal^P.exponent*(H:ℝ)^(1-P.exponent)+
          8*PairBand^2*Mglobal^χ*(H:ℝ)^(1-χ):=by
  intro C PairBand CC Cm CovBudget Kcov νv
  let Bound:=2*Kcov*Mglobal^P.exponent*(H:ℝ)^(1-P.exponent)+8*PairBand^2*Mglobal^χ*(H:ℝ)^(1-χ)
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hCC:0≤CC:=MixedPastWordMoments.momentConstant_nonneg P (k+1) (k+1) 1 _
  have hK:0≤Kcov:=mul_nonneg
    (mul_nonneg (mul_nonneg hCC (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
  have hEe:=MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  let PairMoment:=fun v:ℝ=>∫⁻ω,ENNReal.ofReal (|PairField (k+1) ν χ v ω|^2) ∂μ.prod haarAddCircle
  have hPm:Measurable PairMoment:=
    (ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (RetainedPairedProductEnergy.field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm (k+1) ν χ)).pow_const 2)).lintegral_prod_right' (ν:=μ.prod haarAddCircle)
  have hsection:(∫⁻v in Ioc (0:ℝ) (H:ℝ),∫⁻ω,ENNReal.ofReal (|Field (k+1) v ω|^2) ∂μ.prod haarAddCircle)≤
      ∫⁻v in Ioc (0:ℝ) (H:ℝ),(2:ℝ≥0∞)*(ENNReal.ofReal Kcov*(Ee v)^P.exponent+PairMoment v):=by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    by_cases hwin:v+(h:ℝ)≤(H:ℝ)
    · have hvR:(v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1.le
      have hvH:v.toNNReal+h≤H:=by exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) from by simpa only [hvR] using hwin)
      have hs:=RetainedMovingEnergySection.actual_section_split
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h Z htarget hstop F hF hFm
        hlocal hΛ hH hh hages hrootstop hrootage hcenter hspan hsmallP k hsmall hA0 hν hχ hχβ hjet
        order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov v.toNNReal hvH
      dsimp only at hs
      let Ep:=MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v.toNNReal
      have hEp:0≤Ep:=MixedMovingEnergy.energy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S _
      have hvalid:0≤v ∧ v+(h:ℝ)≤(H:ℝ):=⟨hv.1.le,hwin⟩
      have hepair:PairMoment v=ENNReal.ofReal (∫ω,|Value v.toNNReal (k+1) ν χ ω|^2 ∂μ.prod haarAddCircle):=by
        simp only [PairMoment,RetainedPairedMovingEnergy.field,if_pos hvalid]
        exact (ofReal_integral_eq_lintegral_ofReal hs.2.1 (ae_of_all _ (fun _=>sq_nonneg _))).symm
      have heword:(∫⁻ω,ENNReal.ofReal (|Field (k+1) v ω|^2) ∂μ.prod haarAddCircle)=
          ENNReal.ofReal (∫ω,|WordValue v.toNNReal (k+1) ω|^2 ∂μ.prod haarAddCircle):=by
        simp only [field,if_pos hvalid]
        exact (ofReal_integral_eq_lintegral_ofReal hs.1 (ae_of_all _ (fun _=>sq_nonneg _))).symm
      have hep:ENNReal.ofReal (Ep^P.exponent)=(Ee v)^P.exponent:=by
        simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,indicator_of_mem hv]
        exact (ENNReal.ofReal_rpow_of_nonneg hEp P.exponent_pos.le).symm
      rw [heword,hepair]
      have hhsec:(∫ω,|WordValue v.toNNReal (k+1) ω|^2 ∂μ.prod haarAddCircle)≤
          2*(Kcov*Ep^P.exponent+(∫ω,|Value v.toNNReal (k+1) ν χ ω|^2 ∂μ.prod haarAddCircle)):=hs.2.2
      refine (ENNReal.ofReal_le_ofReal hhsec).trans_eq ?_
      rw [ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤2),
        ENNReal.ofReal_add (mul_nonneg hK (Real.rpow_nonneg hEp _)) (integral_nonneg (fun _=>sq_nonneg _)),
        ENNReal.ofReal_mul hK,hep]
      norm_num
    · have hn:¬(0≤v ∧ v+(h:ℝ)≤(H:ℝ)):=fun hw=>hwin hw.2
      simp only [field,if_neg hn,abs_zero,zero_pow (by decide:(2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
      exact bot_le
  have hβ:=MovingPastFractional.powerWindow_mass hEe P.exponent_pos.le P.exponent_le_one (H:ℝ)
  rw [MovingPastFractional.powerWindow,lintegral_indicator measurableSet_Ioc,
    MixedMovingEnergy.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ hH B1 hBDG1] at hβ
  have hβ':(∫⁻v in Ioc (0:ℝ) (H:ℝ),(Ee v)^P.exponent)≤
      ENNReal.ofReal (Mglobal^P.exponent*(H:ℝ)^(1-P.exponent)):=by
    refine hβ.trans_eq ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
    exact congrArg₂ (fun a b:ℝ≥0∞=>a*b)
      (ENNReal.ofReal_rpow_of_nonneg hM P.exponent_pos.le)
      (ENNReal.ofReal_rpow_of_nonneg H.2 (sub_nonneg.mpr P.exponent_le_one))
  have hpair:=RetainedPairedBandEnergy.actual_global_band_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h Z htarget hstop F hF hFm
    hlocal hΛ hH hh hages hrootstop hrootage hcenter hspan hsmallP k hsmall hA0 hν hχ hχβ hjet
    order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov hhH hη hband
  have hnested:(∫⁻v in Ioc (0:ℝ) (H:ℝ),∫⁻ω,ENNReal.ofReal (|Field (k+1) v ω|^2) ∂μ.prod haarAddCircle)≤ENNReal.ofReal Bound:=by
    refine hsection.trans ?_
    have hsplit:(∫⁻v in Ioc (0:ℝ) (H:ℝ),(2:ℝ≥0∞)*(ENNReal.ofReal Kcov*(Ee v)^P.exponent+PairMoment v))=
        (2:ℝ≥0∞)*((∫⁻v in Ioc (0:ℝ) (H:ℝ),ENNReal.ofReal Kcov*(Ee v)^P.exponent)+
          (∫⁻v in Ioc (0:ℝ) (H:ℝ),PairMoment v)):=by
      calc
        _=(2:ℝ≥0∞)*(∫⁻v in Ioc (0:ℝ) (H:ℝ),ENNReal.ofReal Kcov*(Ee v)^P.exponent+PairMoment v):=by
          convert! lintegral_const_mul (2:ℝ≥0∞)
            (((hEe.pow_const P.exponent).const_mul (ENNReal.ofReal Kcov)).add hPm) using 1
        _=_:=by
          congr 1
          convert! lintegral_add_left ((hEe.pow_const P.exponent).const_mul (ENNReal.ofReal Kcov)) PairMoment using 1
    have hconst:(∫⁻v in Ioc (0:ℝ) (H:ℝ),ENNReal.ofReal Kcov*(Ee v)^P.exponent)=
        ENNReal.ofReal Kcov*(∫⁻v in Ioc (0:ℝ) (H:ℝ),(Ee v)^P.exponent):=by
      convert! lintegral_const_mul (ENNReal.ofReal Kcov) (hEe.pow_const P.exponent) using 1
    rw [hsplit,hconst]
    have hm:=mul_le_mul_right (add_le_add (mul_le_mul_right hβ' (ENNReal.ofReal Kcov)) hpair) (2:ℝ≥0∞)
    refine hm.trans_eq ?_
    have hX:0≤Kcov*(Mglobal^P.exponent*(H:ℝ)^(1-P.exponent)):=
      mul_nonneg hK (mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg H.2 _))
    have hY:0≤4*PairBand^2*Mglobal^χ*(H:ℝ)^(1-χ):=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (Real.rpow_nonneg hM _)) (Real.rpow_nonneg H.2 _)
    change (2:ℝ≥0∞)*(ENNReal.ofReal Kcov*ENNReal.ofReal (Mglobal^P.exponent*(H:ℝ)^(1-P.exponent))+
      ENNReal.ofReal (4*PairBand^2*Mglobal^χ*(H:ℝ)^(1-χ)))=ENNReal.ofReal Bound
    rw [←ENNReal.ofReal_mul hK,←ENNReal.ofReal_add hX hY,
      show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,
      ←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤2)]
    congr 1
    dsimp only [Bound]
    ring
  have hFm2:Measurable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2):=
    (continuous_abs.measurable.comp (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm (k+1))).pow_const 2
  have ht:(∫⁻z:ℝ×(Ω×HeatCircle),ENNReal.ofReal (|Field (k+1) z.1 z.2|^2) ∂νv.prod (μ.prod haarAddCircle))≤ENNReal.ofReal Bound:=by
    calc
      _=(∫⁻v,(∫⁻ω,ENNReal.ofReal (|Field (k+1) v ω|^2) ∂μ.prod haarAddCircle) ∂νv):=by
        apply lintegral_prod (μ:=νv) (ν:=μ.prod haarAddCircle)
        convert! (ENNReal.measurable_ofReal.comp hFm2).aemeasurable using 1
      _≤_:=hnested
  have hi:Integrable (fun z:ℝ×(Ω×HeatCircle)=>|Field (k+1) z.1 z.2|^2) (νv.prod (μ.prod haarAddCircle)):=by
    refine ⟨hFm2.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _))]
    exact ht.trans_lt ENNReal.ofReal_lt_top
  have hb0:0≤Bound:=by dsimp only [Bound];positivity
  refine ⟨hi,(ENNReal.ofReal_le_ofReal_iff hb0).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _))]
  exact ht

end SHE.RetainedMovingRemainderEnergy
