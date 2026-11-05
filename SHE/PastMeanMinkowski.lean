module

public import SHE.PastMeanRMS
public import SHE.PastMeanDampedTime
public import SHE.HilbertFiniteAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastMeanRMS
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure QuarterSpatialEvent PhysicalParentGeometry
open scoped ENNReal
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable {R : ReferenceData} (L : Level R HeatCircle 1)

/-- Minkowski on the original finite old-time cube, with the exact
relative-age trace density and retained current-input small factor. -/
theorem old_time_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (Λ q A0 ν ρ C E χ ε : ℝ) (hΛ : 0<Λ) (hqbase : R.base≤q)
    (hqT : q<T) (hTH : T≤R.horizon) (hA0 : 0≤A0) (hν : 0≤ν)
    (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hC : 0≤C) (hE : 0≤E)
    (hε : 0≤ε) (hεhalf : ε<1/2)
    (F : (Fin k→ℝ)×Ω→V) (hF : Measurable F)
    (hs : ∀ᵐ t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)),
      active L T k q t →
        Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧
        (∫ ω,‖F (t,ω)‖^2 ∂μ)≤
          (GaussianNegativePacket.constant ρ*
            (NativeHeatSpan.clock (PastMeanEnvelope.width (R:=R) T k q t))^(ρ-1/2)*
            PastMeanEnvelope.amplitude L P T k Λ q A0 ν t^2*C)*E^χ)
    (hz : ∀ t,¬active L T k q t → ∀ ω,F (t,ω)=0) :
    let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
    let K:=coefficient P k ρ C*(T-q)^(ρ/2)
    Integrable F (old.prod μ) ∧
      Integrable (fun ω=>‖∫ t,F (t,ω) ∂old‖^2) μ ∧
      (∫ ω,‖∫ t,F (t,ω) ∂old‖^2 ∂μ)≤
        (K*E^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          QuarterRMSTimeFactors.oldTimeBudget P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
            k (T-R.base) (q-R.base) (1/2-ε) A0 ν)^2 := by
  intro old K
  have hK : 0≤K:=mul_nonneg (coefficient_nonneg P k ρ C) (rpow_nonneg (sub_nonneg.mpr hqT.le) _)
  have hell : 0<ControlledOldIntervals.fraction P*P.lower:=
    mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hCs : ∀ j,0≤uniformConstant 1 j:=fun j=>(uniformConstant_pos 1 j).le
  let A : (Fin k→ℝ)→ℝ:=fun t=>K*E^(χ/2)*exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
    PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
      k q (1/2:ℝ) A0 ν (anchor k t)
  have hB:=PastMeanTimeFactors.damped_old_time_budget L P T hT hell (uniformConstant 1) hCs k
    hqbase hqT hTH hA0 hν hΛ hε hεhalf
  have hAi : Integrable A old:=by
    apply (hB.1.const_mul (K*E^(χ/2))).congr
    exact ae_of_all _ (fun _=>(mul_assoc _ _ _).symm)
  have hAm : Measurable A:=by
    apply Measurable.mul
    · exact measurable_const.mul (((((carrier L k).terminal_measurable.comp
        (anchor_measurable k)).sub measurable_const).const_mul (-Λ)).div_const 4 |>.exp)
    · exact (PastMeanTimeFactors.totalIntegrand_measurable L P (ControlledOldIntervals.fraction P*P.lower)
        (uniformConstant 1) k q (1/2:ℝ) A0 ν).comp (anchor_measurable k)
  have hAn (t : Fin k→ℝ) : 0≤A t:=mul_nonneg
    (mul_nonneg (mul_nonneg hK (rpow_nonneg hE _)) (exp_pos _).le)
      (PastMeanTimeFactors.totalIntegrand_nonneg L P hell (uniformConstant 1) hCs k q (1/2:ℝ) A0 ν _)
  have hsec : ∀ᵐ t ∂old,Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧
      (∫ ω,‖F (t,ω)‖^2 ∂μ)≤A t^2 := by
    filter_upwards [hs] with t ht
    by_cases ha : active L T k q t
    · have hh:=ht ha
      have hc:=cap_bound L P T hT k Λ q A0 ν ρ C hρ hρhalf hC t ha
      have he : (E^(χ/2))^2=E^χ:=by
        rw [←Real.rpow_mul_natCast hE]
        congr 1
        ring
      refine ⟨hh.1,hh.2.trans ?_⟩
      have hb:=mul_le_mul_of_nonneg_right hc (rpow_nonneg hE χ)
      have heq :
          (coefficient P k ρ C*(T-q)^(ρ/2)*exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
            PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
              k q (1/2:ℝ) A0 ν (anchor k t))^2*E^χ=A t^2 := by
        dsimp only [A,K]
        rw [←he]
        ring
      exact hb.trans_eq heq
    · have hzero:=hz t ha
      constructor
      · simpa only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
          (integrable_const (0:ℝ) : Integrable (fun _ : Ω=>(0:ℝ)) μ)
      · simp only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,sq_nonneg]
  have hh:=HilbertParameterAverage.finite_energy μ old F hF A hAm hAi hAn
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  apply pow_le_pow_left₀ (integral_nonneg hAn) _ 2
  have heq : A=fun t=>(K*E^(χ/2))*(exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      PastMeanTimeFactors.totalIntegrand L P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
        k q (1/2:ℝ) A0 ν (anchor k t)):=by
    funext t
    exact mul_assoc _ _ _
  rw [heq,integral_const_mul]
  have hb:=mul_le_mul_of_nonneg_left hB.2 (mul_nonneg hK (rpow_nonneg hE (χ/2)))
  simpa only [mul_assoc] using hb

end SHE.PastMeanRMS
