module

public import SHE.PastMeanTimeIntegral
public import SHE.NativeCurrentBudgetFrequency
public import SHE.HilbertFiniteAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.NativeHigherOldTimeEnergy
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure QuarterSpatialEvent PhysicalParentGeometry
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E][InnerProductSpace ℝ E]
  [CompleteSpace E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable {R:ReferenceData}(L:Level R HeatCircle 1)

/-- Original old-time Minkowski with both actual current and past
amplitudes. The relative full observation ages are retained by the
checked finite-assignment integral, before squaring the average. -/
theorem energy (μ:Measure Ω)[IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    {ell:ℝ}(hell:0<ell)(Cs:ℕ→ℝ)(hCs:∀j,0≤Cs j)(k:ℕ)
    {q A0 ν ρ χ Ccur Cpast Eq Ev:ℝ}
    (hqbase:R.base≤q)(hqT:q<T)(hTH:T≤R.horizon)
    (hA0:0≤A0)(hν:0≤ν)(hρ:0≤ρ)(hχ:0≤χ)(hχ1:χ<1)
    (hCcur:0≤Ccur)(hCpast:0≤Cpast)(hEq:0≤Eq)(hEv:0≤Ev)
    (F:((Fin k→ℝ)×Ω)→E)(hF:Measurable F)
    (hs:∀ᵐt∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)),
      active L T k q t→Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧
        (∫ω,‖F (t,ω)‖^2 ∂μ)≤
          ((T-q)^(ρ/2)*(Ccur*Eq^(χ/2)*
            PastMeanTimeFactors.totalIntegrand L P ell Cs k q ((2-χ)/4) A0 ν (anchor k t)+
            Cpast*sqrt Ev*(q-R.base)^(-(1/4:ℝ))*
            PastMeanTimeFactors.totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν (anchor k t)))^2)
    (hz:∀t,¬active L T k q t→∀ω,F (t,ω)=0):
    let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
    Integrable F (old.prod μ) ∧
      Integrable (fun ω=>‖∫t,F (t,ω) ∂old‖^2) μ ∧
      (∫ω,‖∫t,F (t,ω) ∂old‖^2 ∂μ)≤
        ((T-q)^(ρ/2)*(Ccur*Eq^(χ/2)*
          QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-R.base) (q-R.base) ((2-χ)/4) A0 ν+
          Cpast*sqrt Ev*(q-R.base)^(-(1/4:ℝ))*
          QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-R.base) (q-R.base) (1/2:ℝ) A0 ν))^2 :=by
  intro old
  let Icur:=fun t=>PastMeanTimeFactors.totalIntegrand L P ell Cs k q ((2-χ)/4) A0 ν (anchor k t)
  let Ipast:=fun t=>PastMeanTimeFactors.totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν (anchor k t)
  let Kcur:=Ccur*Eq^(χ/2)
  let Kpast:=Cpast*sqrt Ev*(q-R.base)^(-(1/4:ℝ))
  let A:=fun t=>(T-q)^(ρ/2)*(Kcur*Icur t+Kpast*Ipast t)
  have hkc:0≤Kcur:=mul_nonneg hCcur (rpow_nonneg hEq _)
  have hkp:0≤Kpast:=mul_nonneg (mul_nonneg hCpast (sqrt_nonneg _)) (rpow_nonneg (sub_nonneg.mpr hqbase) _)
  have hbc:=PastMeanTimeFactors.old_time_budget L P T hT hell Cs hCs k hqbase hqT hTH
    (by linarith : 0<(2-χ)/4) (by linarith : (2-χ)/4≤1) hA0 hν
  have hbp:=PastMeanTimeFactors.old_time_budget L P T hT hell Cs hCs k hqbase hqT hTH
    (by norm_num : 0<(1/2:ℝ)) (by norm_num : (1/2:ℝ)≤1) hA0 hν
  have hAi:Integrable A old:=((hbc.1.const_mul Kcur).add (hbp.1.const_mul Kpast)).const_mul _
  have hIm(fresh:ℝ):Measurable (fun t=>PastMeanTimeFactors.totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t)):=by
    have he:(fun t=>PastMeanTimeFactors.totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t))=
        fun t=>∑i:Fin (GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).length,
          PastMeanTimeFactors.activeFactor L P ell Cs k q fresh A0 ν
            ((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).get i) (anchor k t):=
      funext (fun _=>PastMeanTimeFactors.totalIntegrand_eq_sum L P ell Cs k q fresh A0 ν _)
    rw [he]
    exact Finset.measurable_sum _ (fun i _=>(PastMeanTimeFactors.activeFactor_measurable L P ell Cs k q fresh A0 ν _).comp (anchor_measurable k))
  have hAm:Measurable A:=measurable_const.mul
    ((measurable_const.mul (hIm ((2-χ)/4))).add (measurable_const.mul (hIm (1/2:ℝ))))
  have hIt(fresh:ℝ)(t:Fin k→ℝ):0≤PastMeanTimeFactors.totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t):=by
    rw [PastMeanTimeFactors.totalIntegrand_eq_sum]
    exact Finset.sum_nonneg (fun i _=>PastMeanTimeFactors.activeFactor_nonneg L P hell Cs hCs k q fresh A0 ν _ _)
  have hAn(t):0≤A t:=mul_nonneg (rpow_nonneg (sub_nonneg.mpr hqT.le) _)
    (add_nonneg (mul_nonneg hkc (hIt _ t)) (mul_nonneg hkp (hIt _ t)))
  have hsec:∀ᵐt∂old,Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧ (∫ω,‖F (t,ω)‖^2 ∂μ)≤A t^2:=by
    filter_upwards [hs] with t ht
    by_cases ha:active L T k q t
    · exact ht ha
    · have he:=hz t ha
      simp only [he,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero]
      exact ⟨integrable_const _,sq_nonneg _⟩
  have hh:=HilbertParameterAverage.finite_energy μ old F hF A hAm hAi hAn
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  apply pow_le_pow_left₀ (integral_nonneg hAn) _ 2
  rw [show A=fun t=>(T-q)^(ρ/2)*(Kcur*Icur t+Kpast*Ipast t) from rfl,
    integral_const_mul,integral_add (hbc.1.const_mul Kcur) (hbp.1.const_mul Kpast),integral_const_mul,integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hbc.2 hkc) (mul_le_mul_of_nonneg_left hbp.2 hkp))
    (rpow_nonneg (sub_nonneg.mpr hqT.le) _)

end SHE.NativeHigherOldTimeEnergy
