module

public import SHE.NativeObservationCaps
public import SHE.NativeStoppedBracket
public import SHE.TimeCausalPowers

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeVariableTerminalCap
open MeasureTheory Set PredictableL2 StoppedFourier ProfileVariance
open scoped ENNReal NNReal
variable {P Ω:Type*} [MeasurableSpace P] [MeasurableSpace Ω]

/-- The positive endpoint cap is integrable on the SAME full time
measure, uniformly over the terminal time. -/
theorem mass (H c:ℝ≥0)(hcH:c≤H)(hc1:(c:ℝ)≤1){M:ℝ}(hM:0≤M):
    (∫⁻s,ENNReal.ofReal (if s<c then NativeObservationCaps.cap M ((c:ℝ)-(s:ℝ)) else 0) ∂timeMeasure H)≤
      ENNReal.ofReal (upperConstant*M):=by
  let K:=M*(1+heatConstant)
  have hK:0≤K:=mul_nonneg hM (by linarith [heatConstant_pos])
  calc
    _≤∫⁻s,ENNReal.ofReal K*(Iio c).indicator
        (fun r:ℝ≥0=>ENNReal.ofReal (((c:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) s ∂timeMeasure H:=by
      apply lintegral_mono
      intro s
      dsimp only
      by_cases hsc:s<c
      · rw [ite_eq_left hsc,Set.indicator_of_mem (show s∈Iio c from hsc),←ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        have hscR:(s:ℝ)<(c:ℝ):=by exact_mod_cast hsc
        have hp:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr hscR)
          (show (c:ℝ)-(s:ℝ)≤1 by linarith [s.2]) (by norm_num:-(1/2:ℝ)≤0)
        unfold NativeObservationCaps.cap K
        nlinarith [mul_le_mul_of_nonneg_left hp hM]
      · rw [ite_eq_right hsc,Set.indicator_of_notMem (show s∉Iio c from hsc)]
        simp
    _=ENNReal.ofReal (upperConstant*M*(c:ℝ)^(1/2:ℝ)):=by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Iio,
        NativeStoppedBracket.timeMeasure_before hcH,
        causal_rpow_mass (by norm_num: (-1:ℝ) < -(1/2:ℝ))]
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      rw [←ENNReal.ofReal_mul hK]
      congr 1
      unfold K ProfileVariance.upperConstant
      ring
    _≤_:=ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right
      (mul_nonneg (by unfold ProfileVariance.upperConstant;nlinarith [heatConstant_pos]) hM)
      (Real.rpow_le_one c.2 hc1 (by norm_num:0≤(1/2:ℝ))))

/-- One original-history/current/sample integrable majorant controls all
positive heat regularizations. The terminal is a genuine Borel history
function and can approach the current time. -/
theorem integrable (ν:Measure P)[IsFiniteMeasure ν](μ:Measure Ω)[IsProbabilityMeasure μ]
    (H:ℝ≥0)(T:P→ℝ)(hT:Measurable T)(hT0:∀p,0≤T p)(hTH:∀p,T p≤(H:ℝ))
    (hT1:∀p,T p≤1){M:ℝ}(hM:0≤M):
    Integrable (fun z:P×(ℝ≥0×Ω)=>
      if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap M (T z.1-(z.2.1:ℝ)) else 0)
        (ν.prod (energyMeasure μ H)):=by
  letI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  let F:=fun z:P×(ℝ≥0×Ω)=>
    if (z.2.1:ℝ)<T z.1 then NativeObservationCaps.cap M (T z.1-(z.2.1:ℝ)) else 0
  have hm:Measurable F:=by
    have hage:Measurable (fun z:P×(ℝ≥0×Ω)=>T z.1-(z.2.1:ℝ)):=
      (hT.comp measurable_fst).sub (measurable_coe_nnreal_real.comp measurable_snd.fst)
    have hc:Measurable (fun z:P×(ℝ≥0×Ω)=>NativeObservationCaps.cap M (T z.1-(z.2.1:ℝ))):=by
      unfold NativeObservationCaps.cap
      exact measurable_const.mul (measurable_const.add (measurable_const.mul (hage.pow_const (-(1/2:ℝ)))))
    exact hc.ite
      (measurableSet_lt (measurable_coe_nnreal_real.comp measurable_snd.fst) (hT.comp measurable_fst)) measurable_const
  have hn:∀z,0≤F z:=by
    intro z
    dsimp only [F]
    split_ifs with hz
    · exact NativeObservationCaps.cap_nonneg hM (sub_pos.mpr hz)
    · exact le_rfl
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (Filter.Eventually.of_forall hn)).mp
  have he:(∫⁻z,ENNReal.ofReal (F z) ∂ν.prod (energyMeasure μ H))≤
      ENNReal.ofReal (upperConstant*M)*ν univ:=by
    rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
    calc
      _≤∫⁻p,ENNReal.ofReal (upperConstant*M) ∂ν:=by
        apply lintegral_mono
        intro p
        let c:ℝ≥0:=(T p).toNNReal
        have hc:(c:ℝ)=T p:=Real.coe_toNNReal _ (hT0 p)
        have hcH:c≤H:=by exact_mod_cast (show (c:ℝ)≤H by rw [hc];exact hTH p)
        have hc1:(c:ℝ)≤1:=by rw [hc];exact hT1 p
        change (∫⁻z,ENNReal.ofReal (F (p,z)) ∂(timeMeasure H).prod μ)≤_
        rw [lintegral_prod (fun z:ℝ≥0×Ω=>ENNReal.ofReal (F (p,z)))
          ((hm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal.aemeasurable)]
        simp only [F,lintegral_const,measure_univ,IsProbabilityMeasure.measure_univ,mul_one]
        convert mass H c hcH hc1 hM using 1
        congr 1
        funext s
        simp only [F,←hc,NNReal.coe_lt_coe]
      _=_:=lintegral_const _
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) he

end SHE.NativeVariableTerminalCap
