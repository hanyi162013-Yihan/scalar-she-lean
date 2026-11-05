module

public import SHE.PastSignedEndpointTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.PastSignedEndpointTime
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure ActualMeanKernel ScalarMeanEnvelope
  QuarterSpatialEvent PhysicalParentGeometry RawTraceTimeEnvelope
open Classical
local instance pastSignedEndpointBudget_period : Fact (0<2*π) := ⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)

/-- The literal good/bad endpoint RMS, with its actual inactive region
zeroed before integration under the original old-time measure. -/
def value (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(k:ℕ)
    (Λ q A0 ν J ρ η lam ε U C tail E:ℝ)(t:Fin k→ℝ):ℝ:=
  if active L T k q t then
    let δ:=quarterTraceTime (R:=R) T k q t
    let w:=PastMeanEnvelope.width (R:=R) T k q t
    let D:=PastMeanAmplitude.damped L P k Λ q A0 ν (anchor k t)*ScalarMeanEnvelope.massCoefficient k 1*sqrt δ
    RawTraceTimeEnvelope.goodAmplitude J ρ η (lam^ε) D δ w*sqrt E+
      RawTraceTimeEnvelope.badAmplitude U C D δ lam tail
  else 0

theorem value_measurable (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(k:ℕ)
    (Λ q A0 ν J ρ η lam ε U C tail E:ℝ):
    Measurable (value L P T k Λ q A0 ν J ρ η lam ε U C tail E):=by
  have hδ:Measurable (fun t:Fin k→ℝ=>quarterTraceTime (R:=R) T k q t):=
    quarterTraceTime_measurable T k measurable_const measurable_id
  have hw:=PastMeanEnvelope.width_measurable (R:=R) T k q
  have hD:Measurable (fun t:Fin k→ℝ=>PastMeanAmplitude.damped L P k Λ q A0 ν (anchor k t)*
      ScalarMeanEnvelope.massCoefficient k 1*sqrt (quarterTraceTime (R:=R) T k q t)):=
    (((PastMeanAmplitude.damped_measurable L P k Λ q A0 ν).comp (anchor_measurable k)).mul_const _).mul hδ.sqrt
  unfold value RawTraceTimeEnvelope.goodAmplitude RawTraceTimeEnvelope.badAmplitude
  apply Measurable.ite (active_measurableSet L T k q)
  · exact (((((measurable_const.mul hD).mul (hδ.pow_const _)).mul (hw.pow_const _)).mul_const _).add
      (((measurable_const.mul hD).mul (hδ.pow_const _)).mul_const _))
  · exact measurable_const

theorem value_nonneg (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    (k:ℕ)(Λ q A0 ν J ρ η lam ε U C tail E:ℝ)(hlam:0≤lam)(t:Fin k→ℝ):
    0≤value L P T k Λ q A0 ν J ρ η lam ε U C tail E t:=by
  unfold value
  split_ifs with ha
  · have hδ:=quarterTraceTime_nonneg (R:=R) T k q t
    have hw:0≤PastMeanEnvelope.width (R:=R) T k q t:=(PastMeanEnvelope.width_pos L T hT k q t ha.2).le
    have hD:0≤PastMeanAmplitude.damped L P k Λ q A0 ν (anchor k t)*ScalarMeanEnvelope.massCoefficient k 1*
        sqrt (quarterTraceTime (R:=R) T k q t):=
      mul_nonneg (mul_nonneg (PastMeanAmplitude.damped_nonneg L P k Λ q A0 ν _)
        (ScalarMeanEnvelope.massCoefficient_nonneg k zero_le_one)) (sqrt_nonneg _)
    exact add_nonneg (mul_nonneg (goodAmplitude_nonneg J ρ η (rpow_nonneg hlam _) hD hδ hw) (sqrt_nonneg _))
      (badAmplitude_nonneg U C tail hD hδ hlam)
  · exact le_rfl

/-- Original-oldtime Minkowski integrates the literal signed endpoint
RMS before its square, using both genuine fresh gap degrees. -/
theorem old_time_bound (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    (k:ℕ)(Λ q A0 ν J ρ η lam ε U C tail E:ℝ)
    (hΛ:0≤Λ)(hρ:0≤ρ)(hη:0≤η)(hρη:ρ+η<1)(hlam:0≤lam)
    (hqbase:R.base≤q)(hqT:q<T)(hTH:T≤R.horizon)(hA0:0≤A0)(hν:0≤ν):
    let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
    Integrable (value L P T k Λ q A0 ν J ρ η lam ε U C tail E) old ∧
      (∫t,value L P T k Λ q A0 ν J ρ η lam ε U C tail E t ∂old)≤
        goodCoefficient P k J ρ η*lam^ε*(T-q)^((ρ+η)/2)*sqrt E*
          QuarterRMSTimeFactors.oldTimeBudget P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
            k (T-R.base) (q-R.base) (freshDegree ρ η) A0 ν+
        badCoefficient P k U C*lam^(-tail/2)*
          QuarterRMSTimeFactors.oldTimeBudget P (ControlledOldIntervals.fraction P*P.lower) (uniformConstant 1)
            k (T-R.base) (q-R.base) (1/2:ℝ) A0 ν:=by
  intro old
  let ell:=ControlledOldIntervals.fraction P*P.lower
  have hell:0<ell:=mul_pos (ControlledOldIntervals.fraction_pos P) P.lower_pos
  have hCs(j):0≤uniformConstant 1 j:=(uniformConstant_pos 1 j).le
  let Ic:=fun t=>PastMeanTimeFactors.totalIntegrand L P ell (uniformConstant 1)
    k q (freshDegree ρ η) A0 ν (anchor k t)
  let Ib:=fun t=>PastMeanTimeFactors.totalIntegrand L P ell (uniformConstant 1)
    k q (1/2:ℝ) A0 ν (anchor k t)
  let G:=goodCoefficient P k J ρ η*lam^ε*(T-q)^((ρ+η)/2)*sqrt E
  let B:=badCoefficient P k U C*lam^(-tail/2)
  have hG:0≤G:=mul_nonneg (mul_nonneg (mul_nonneg (goodCoefficient_nonneg P k J ρ η)
    (rpow_nonneg hlam _)) (rpow_nonneg (sub_pos.mpr hqT).le _)) (sqrt_nonneg _)
  have hB:0≤B:=mul_nonneg (badCoefficient_nonneg P k U C) (rpow_nonneg hlam _)
  have hc:=PastMeanTimeFactors.old_time_budget L P T hT hell (uniformConstant 1) hCs k hqbase hqT hTH
    (freshDegree_pos hρη) (freshDegree_le_one hρ hη) hA0 hν
  have hb:=PastMeanTimeFactors.old_time_budget L P T hT hell (uniformConstant 1) hCs k hqbase hqT hTH
    (by norm_num:0<(1/2:ℝ)) (by norm_num:(1/2:ℝ)≤1) hA0 hν
  have hi:Integrable (fun t=>G*Ic t+B*Ib t) old:=(hc.1.const_mul G).add (hb.1.const_mul B)
  have hdom(t):value L P T k Λ q A0 ν J ρ η lam ε U C tail E t≤G*Ic t+B*Ib t:=by
    by_cases ha:active L T k q t
    · simpa only [value,if_pos ha,Ic,Ib,G,B,ell] using
        amplitude_bound L P T hT k Λ q A0 ν J ρ η lam ε U C tail E hΛ hρ hη hlam t ha
    · simp only [value,if_neg ha]
      exact add_nonneg
        (mul_nonneg hG (PastMeanTimeFactors.totalIntegrand_nonneg L P hell (uniformConstant 1) hCs k q _ A0 ν _))
        (mul_nonneg hB (PastMeanTimeFactors.totalIntegrand_nonneg L P hell (uniformConstant 1) hCs k q _ A0 ν _))
  have hv:Integrable (value L P T k Λ q A0 ν J ρ η lam ε U C tail E) old:=
    hi.mono' (value_measurable L P T k Λ q A0 ν J ρ η lam ε U C tail E).aestronglyMeasurable
      (ae_of_all _ (fun t=>by rw [Real.norm_of_nonneg (value_nonneg L P T hT k Λ q A0 ν J ρ η lam ε U C tail E hlam t)];exact hdom t))
  refine ⟨hv,?_⟩
  have hh:=integral_mono hv hi hdom
  rw [integral_add (hc.1.const_mul G) (hb.1.const_mul B),integral_const_mul,integral_const_mul] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hc.2 hG) (mul_le_mul_of_nonneg_left hb.2 hB))

end SHE.PastSignedEndpointTime
