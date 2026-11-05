module

public import SHE.MixedMovingEnergy
public import SHE.ControlledPairedTimeTranslation
public import SHE.MixedPairedClockIntegrals
public import SHE.MixedPastTerminalPairedHistoryEnergy
public import SHE.RetainedPairedMovingSection
public import SHE.RetainedPairedMovingKernel
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

namespace SHE.RetainedPairedMovingEnergy
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingPairedRemainderEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingPairedRemainderEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingPairedRemainderEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance movingPairedRemainderEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingPairedRemainderEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingPairedRemainderEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingPairedRemainderEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingPairedRemainderEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingPairedRemainderEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingPairedRemainderEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingPairedRemainderEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingPairedRemainderEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

/-- The literal finite paired remainder on complete moving windows;
the extension outside the physical window is zero. -/
def field (k:ℕ) (ν χ:ℝ) (v:ℝ) (ω:Ω×HeatCircle):ℝ:=
  if 0≤v ∧ v+(h:ℝ)≤(H:ℝ) then Value v.toNNReal k ν χ ω else 0

local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Actual finite-depth paired terminal remainder after old
history with output retained averaging and moving-past integration. The RHS contains the
TRUE global difference energy to power chi and the explicit finite
root/rough time budget. No pointwise current-energy cap is used in
the quantitative result. -/
theorem actual_global_energy
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
    (hBDG1:StandardTerminalBDGPower 1 J B1) (hBDGcov:StandardTerminalBDGPower (k+3) J Bcov):
    let Budget:=PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ω,ENNReal.ofReal (|Field (k+1) ν χ v ω|^2) ∂μ.prod AddCircle.haarAddCircle)≤
      ENNReal.ofReal (4*Budget^2*Mglobal^χ*(H:ℝ)^(1-χ)):=by
  intro Budget
  let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))
  let A:=fun t=>RMS (k+1) t ν χ A0 order B0
  let K:=fun t=>ENNReal.ofReal (2*Budget*A t)
  let Q:=Clock (k+1)
  let C:=ENNReal.ofReal (2*Budget^2*Mglobal^χ*(H:ℝ)^(1-χ))
  have hχ1:χ≤1:=hχβ.le.trans P.exponent_le_one
  have hA(t):0≤A t:=MixedPastTerminalRMS.amplitude_nonneg
    (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=h) (hvb:=bot_le)
    (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
    (k+1) t ν χ A0 order B0
  have hmass:(∫t,A t ∂η)≤Budget:=by
    simpa only [NNReal.coe_zero,sub_zero] using
      ControlledTerminalRMSMass.mass_bound P haP Λ 0 h bot_le Z htarget hstop F hF hFm
        κ M hh k hχ.le hχβ hA0 hν order B0
  have hB:0≤Budget:=(integral_nonneg hA).trans hmass
  have hKm:Measurable K:=ENNReal.measurable_ofReal.comp
    ((MixedPastTerminalRMS.amplitude_measurable
      (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=h) (hvb:=bot_le)
      (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
      (k+1) ν χ A0 order B0).const_mul _)
  have hQm:Measurable Q:=MixedPairedCurrentClock.clock_measurable
    (Λ:=Λ) (P:=P) (haP:=haP) (h:=h) (Z:=Z) (htarget:=htarget) (hstop:=hstop)
    (F:=F) (hF:=hF) (hFm:=hFm) (k+1)
  have hEe:Measurable Ee:=MixedMovingEnergy.ennEnergy_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hcurr:Measurable (fun z:ℝ×(Fin (k+1)→ℝ)=>
      K z.2*MovingPastFractional.powerWindow (H:ℝ) χ Ee (z.1+Q z.2)):=
    (hKm.comp measurable_snd).mul
      ((MovingPastFractional.powerWindow_measurable hEe (H:ℝ) χ).comp
        (measurable_fst.add (hQm.comp measurable_snd)))
  have hpast:Measurable (fun z:ℝ×(Fin (k+1)→ℝ)=>K z.2*(Ee z.1)^χ):=
    (hKm.comp measurable_snd).mul ((hEe.comp measurable_fst).pow_const χ)
  have hs:(∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ω,ENNReal.ofReal (|Field (k+1) ν χ v ω|^2) ∂μ.prod AddCircle.haarAddCircle)≤
      ∫⁻v in Ioc (0:ℝ) (H:ℝ),∫⁻t,K t*
        (MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t)+(Ee v)^χ) ∂η:=by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    by_cases hwin:v+(h:ℝ)≤(H:ℝ)
    · have hcoe:(v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1.le
      have hvH:v.toNNReal+h≤H:=by
        exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) from by simpa only [hcoe] using hwin)
      have hsec:=RetainedPairedMovingKernel.actual_kernel_energy
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h Z htarget hstop F hF hFm
        hlocal hΛ hH hh hages hrootstop hrootage hcenter hspan hsmallP k hsmall hA0 hν hχ hχβ hjet
        order horder ho0 ho1 B0 B1 Bcov hBDG hBDG1 hBDGcov v.toNNReal hvH
      let E:=fun t=>MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        (v+Q t).toNNReal
      let Ep:=MixedMovingEnergy.energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v.toNNReal
      have hEc(t):0≤E t:=MixedMovingEnergy.energy_nonneg
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S _
      have hEp:0≤Ep:=MixedMovingEnergy.energy_nonneg
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S _
      have hcur(t):ENNReal.ofReal ((E t)^χ)=
          MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t):=by
        have he:=MixedPairedCurrentClock.current_power
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
          v.toNNReal (by exact_mod_cast (show (0:ℝ)<(v.toNNReal:ℝ) from by simpa only [hcoe] using hv.1))
          hvH (k+1) t hχ.le
        rw [MixedPairedCurrentClock.currentEnergy_translation
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
          v.toNNReal (k+1) t] at he
        simpa only [hcoe] using he
      have hp:ENNReal.ofReal (Ep^χ)=(Ee v)^χ:=by
        simp only [MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,indicator_of_mem hv]
        exact (ENNReal.ofReal_rpow_of_nonneg hEp hχ.le).symm
      have hkg:Integrable (fun t=>2*Budget*A t*((E t)^χ+Ep^χ)) η:=by
        simpa only [hcoe] using hsec.1
      have hki(t):0≤2*Budget*A t*((E t)^χ+Ep^χ):=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (hA t))
          (add_nonneg (rpow_nonneg (hEc t) _) (rpow_nonneg hEp _))
      have hvalid:0≤v ∧ v+(h:ℝ)≤(H:ℝ):=⟨hv.1.le,hwin⟩
      simp only [field,if_pos hvalid]
      rw [←ofReal_integral_eq_lintegral_ofReal hsec.2.1 (ae_of_all _ (fun _=>sq_nonneg _))]
      calc
        _≤ENNReal.ofReal (∫t,2*Budget*A t*((E t)^χ+Ep^χ) ∂η):=by
          apply ENNReal.ofReal_le_ofReal
          simpa only [hcoe] using hsec.2.2
        _=(∫⁻t,ENNReal.ofReal (2*Budget*A t*((E t)^χ+Ep^χ)) ∂η):=
          ofReal_integral_eq_lintegral_ofReal hkg (ae_of_all _ hki)
        _=_:=by
          apply lintegral_congr
          intro t
          rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hB) (hA t)),
            ENNReal.ofReal_add (rpow_nonneg (hEc t) _) (rpow_nonneg hEp _),hcur t,hp]
    · have hn:¬(0≤v ∧ v+(h:ℝ)≤(H:ℝ)):=fun hvv=>hwin hvv.2
      have hf(ω:Ω×HeatCircle):Field (k+1) ν χ v ω=0:=by simp only [field,if_neg hn]
      simp_rw [hf]
      simp only [abs_zero,zero_pow (by decide:(2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
      exact bot_le
  have hb:=MovingPairedRMSBudget.actual_bounds
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ P haP h Z htarget hstop F hF hFm
    hΛ hH hh B1 hBDG1 k hχ.le hχβ hχ1 hA0 hν order B0
  have hsplit:(∫⁻v in Ioc (0:ℝ) (H:ℝ),∫⁻t,K t*
      (MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t)+(Ee v)^χ) ∂η)=
      (∫⁻v in Ioc (0:ℝ) (H:ℝ),∫⁻t,K t*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t) ∂η)+
      (∫⁻v in Ioc (0:ℝ) (H:ℝ),∫⁻t,K t*(Ee v)^χ ∂η):=by
    have hi(v:ℝ):(∫⁻t,K t*(MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t)+(Ee v)^χ) ∂η)=
        (∫⁻t,K t*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t) ∂η)+
          (∫⁻t,K t*(Ee v)^χ ∂η):=by
      simp_rw [mul_add]
      exact lintegral_add_left (hcurr.comp ((measurable_const (a:=v)).prodMk measurable_id))
        (fun t=>K t*(Ee v)^χ)
    simp_rw [hi]
    exact lintegral_add_left (hcurr.lintegral_prod_right' (ν:=η))
      (fun v=>∫⁻t,K t*(Ee v)^χ ∂η)
  apply hs.trans
  rw [hsplit]
  have hsum:(_+_)≤C+C:=add_le_add hb.2 hb.1
  refine hsum.trans_eq ?_
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hcost:0≤2*Budget^2*Mglobal^χ*(H:ℝ)^(1-χ):=by positivity
  dsimp only [C]
  rw [←ENNReal.ofReal_add hcost hcost]
  congr 1
  ring

end SHE.RetainedPairedMovingEnergy

