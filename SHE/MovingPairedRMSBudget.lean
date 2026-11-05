module

public import SHE.MixedMovingEnergy
public import SHE.MovingParameterFractional
public import SHE.ControlledWordTimeShift
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

namespace SHE.MovingPairedRMSBudget
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance movingPairedRMSBudget_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingPairedRMSBudget_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance movingPairedRMSBudget_instance3 : MeasurableSpace RealL2 := borel _
local instance movingPairedRMSBudget_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance movingPairedRMSBudget_instance5 : MeasurableSpace CircleL2 := borel _
local instance movingPairedRMSBudget_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingPairedRMSBudget_instance7 : MeasurableSpace RealHaarInput := borel _
local instance movingPairedRMSBudget_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingPairedRMSBudget_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingPairedRMSBudget_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance movingPairedRMSBudget_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance movingPairedRMSBudget_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
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

include hIJ₀ hIJ₁ in
/-- The explicit finite paired RMS budget averages into the TRUE
global current/past difference energy, without a supremum substitution.
The parameter is the ENTIRE original old-time array. -/
theorem actual_bounds (hΛ:0≤Λ) (hH:(H:ℝ)≤1) (hh:0<h)
    (Bfirst:ℝ≥0) (hBDGfirst:StandardTerminalBDGPower 1 J Bfirst)
    (k:ℕ) {χ A0 ν:ℝ} (hχ:0≤χ) (hχβ:χ<P.exponent) (hχ1:χ≤1)
    (hA0:0≤A0) (hν:0≤ν) (order:ℕ) (B0:ℝ≥0):
    let η:=Measure.pi (fun _:Fin (k+1)=>volume.restrict (Ioc (0:ℝ) (h:ℝ)))
    let A:=fun t=>RMS (k+1) t ν χ A0 order B0
    let Budget:=PairedRMSTimeBudget.total P κ M (ControlledOldIntervals.fraction P*P.lower)
      (PhysicalScoreChain.uniformConstant 1) (k+1) h χ A0 ν order B0
    let Q:=fun t=>(carrier Rel (k+1)).terminal (MixedPastTerminalSlotSpatial.anchor (k+1) t)
    let K:=fun t=>ENNReal.ofReal (2*Budget*A t)
    let Cost:=ENNReal.ofReal (2*Budget^2*Mglobal^χ*(H:ℝ)^(1-χ))
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ t,K t*(Ee v)^χ ∂η)≤Cost ∧
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ t,K t*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+Q t) ∂η)≤Cost:=by
  intro η A Budget Q K Cost
  have hAi:Integrable A η:=MixedPastTerminalRMS.amplitude_integrable
    (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=h) (hvb:=bot_le)
    (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
    hh k hA0 hν hχ hχβ order B0
  have hAm:Measurable A:=MixedPastTerminalRMS.amplitude_measurable
    (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=h) (hvb:=bot_le)
    (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
    (k+1) ν χ A0 order B0
  have hA(t):0≤A t:=MixedPastTerminalRMS.amplitude_nonneg
    (κ:=κ) (M:=M) (Λ:=Λ) (P:=P) (haP:=haP) (v:=0) (b:=h) (hvb:=bot_le)
    (Z:=Z) (htarget:=htarget) (hstop:=hstop) (F:=F) (hF:=hF) (hFm:=hFm)
    (k+1) t ν χ A0 order B0
  have hmassA:(∫t,A t ∂η)≤Budget:=by
    simpa only [NNReal.coe_zero,sub_zero] using
      ControlledTerminalRMSMass.mass_bound P haP Λ 0 h bot_le Z htarget hstop F hF hFm
        κ M hh k hχ hχβ hA0 hν order B0
  have hBudget:0≤Budget:=(integral_nonneg hA).trans hmassA
  have hKm:Measurable K:=ENNReal.measurable_ofReal.comp (hAm.const_mul _)
  have hqm:Measurable Q:=(carrier Rel (k+1)).terminal_measurable.comp
    ((HistoryProductMeasure.separated_measurable (k+1)).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hmassK:(∫⁻t,K t ∂η)≤ENNReal.ofReal (2*Budget^2):=by
    rw [←ofReal_integral_eq_lintegral_ofReal (hAi.const_mul (2*Budget))
      (ae_of_all _ (fun t=>mul_nonneg (mul_nonneg (by norm_num) hBudget) (hA t))),integral_const_mul]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_left hmassA (mul_nonneg (by norm_num : (0:ℝ)≤2) hBudget)]
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hcost:ENNReal.ofReal (2*Budget^2)*
      (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))=Cost:=by
    have hpM:ENNReal.ofReal Mglobal^χ=ENNReal.ofReal (Mglobal^χ):=
      ENNReal.ofReal_rpow_of_nonneg hM hχ
    have hpH:(ENNReal.ofReal (H:ℝ))^(1-χ)=ENNReal.ofReal ((H:ℝ)^(1-χ)):=
      ENNReal.ofReal_rpow_of_nonneg H.2 (sub_nonneg.mpr hχ1)
    rw [hpM,hpH,
      ←ENNReal.ofReal_mul (rpow_nonneg hM χ),
      ←ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg Budget))]
    congr 1
    ring
  have hp:=MovingParameterFractional.past η K Ee hKm
    (MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) hχ hχ1 (H:ℝ)
  have hc:=MovingParameterFractional.current η K Q Ee hKm hqm
    (MixedMovingEnergy.ennEnergy_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) hχ hχ1 (H:ℝ)
  rw [MixedMovingEnergy.real_mass_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH Bfirst hBDGfirst] at hp hc
  constructor
  · exact hp.trans ((show (∫⁻ t,K t ∂η)*
        (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))≤
        ENNReal.ofReal (2*Budget^2)*(ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)) from by
        gcongr).trans_eq hcost)
  · exact hc.trans ((show (∫⁻ t,K t ∂η)*
        (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))≤
        ENNReal.ofReal (2*Budget^2)*(ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ)) from by
        gcongr).trans_eq hcost)

end SHE.MovingPairedRMSBudget

