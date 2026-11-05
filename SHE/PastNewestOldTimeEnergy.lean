module
public import SHE.PastNewestTotalTime
public import SHE.HilbertFiniteAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.PastNewestTimeIntegral
open Set MeasureTheory Real GaussianAssignmentBlocks PhysicalAssignmentGapScale AllocatedAssignmentKernel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure CoveredHistoryGeometry
open scoped BigOperators
variable {X:Type}{Ω:Type*}[MeasurableSpace X][MeasurableSpace Ω]{R:ReferenceData}{n:ℕ}(L:Level R X n)

/-- Old-time averaging precedes the sample square. The finite constant
is chosen before the error size and before the random newest-error field. -/
theorem old_time_energy (μ:Measure Ω)[IsProbabilityMeasure μ]
    (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    {ell:ℝ}(hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(x:X)(z:Fin k→StoppedFourier.HeatCircle)
    {q A0 ν:ℝ}(hqb:R.base≤q)(hqT:q<T)(hTH:T≤R.horizon)(hA:0≤A0)(hν:0≤ν):
    ∃K:ℝ,0≤K ∧
      K=(∫t,activeTotal L P ell C k q (P.exponent/8) A0 ν (separated k (x,t,z))
        ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
      ∀ε D:ℝ,0≤ε→0≤D→∀F:(Fin k→ℝ)×Ω→ℝ,Measurable F→
      (∀ᵐt∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)),
        StrictHistory L k (separated k (x,t,z)) ∧ q<(carrier L k).terminal (separated k (x,t,z))→
          Integrable (fun ω=>|F (t,ω)|^2) μ ∧
          (∫ω,|F (t,ω)|^2 ∂μ)≤ε^2*D*timeWeight L ell C k (separated k (x,t,z))^2*
            PastWordTimeFields.total L P k (separated k (x,t,z)) A0 ν*
              ((carrier L k).terminal (separated k (x,t,z))-q)^(P.exponent/4-2))→
      (∀t,¬(StrictHistory L k (separated k (x,t,z)) ∧ q<(carrier L k).terminal (separated k (x,t,z)))→
        ∀ω,F (t,ω)=0)→
      let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
      Integrable F (old.prod μ) ∧ Integrable (fun ω=>|∫t,F (t,ω) ∂old|^2) μ ∧
        (∫ω,|∫t,F (t,ω) ∂old|^2 ∂μ)≤ε^2*D*K^2:=by
  let old:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let A:(Fin k→ℝ)→ℝ:=fun t=>activeTotal L P ell C k q (P.exponent/8) A0 ν (separated k (x,t,z))
  have hf:0<P.exponent/8:=div_pos P.exponent_pos (by norm_num)
  have hf1:P.exponent/8≤1:=by linarith [P.exponent_le_one]
  have hb:=actual_total_integral_bound L P T hT hell C hC k x z hqb hqT hTH hf hf1 hA hν
  have hAi:Integrable A old:=hb.1
  have hAm:Measurable A:=(activeTotal_measurable L P ell C k q (P.exponent/8) A0 ν).comp
    ((separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hAn(t:Fin k→ℝ):0≤A t:=by
    unfold A activeTotal
    split_ifs with ht
    · exact mul_nonneg (mul_nonneg (rpow_nonneg (sub_pos.mpr ht.2).le _)
        (timeWeight_nonneg L hell C hC k _ ht.1)) (sqrt_nonneg _)
    · exact le_rfl
  refine ⟨∫t,A t ∂old,integral_nonneg hAn,rfl,?_⟩
  intro ε D hε hD F hF hs hz
  dsimp only
  let B:(Fin k→ℝ)→ℝ:=fun t=>ε*sqrt D*A t
  have hBi:Integrable B old:=hAi.const_mul _
  have hBm:Measurable B:=measurable_const.mul hAm
  have hBn(t):0≤B t:=mul_nonneg (mul_nonneg hε (sqrt_nonneg _)) (hAn t)
  have hsec:∀ᵐt∂old,Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧
      (∫ω,‖F (t,ω)‖^2 ∂μ)≤B t^2:=by
    filter_upwards [hs] with t ht
    by_cases ha:StrictHistory L k (separated k (x,t,z)) ∧ q<(carrier L k).terminal (separated k (x,t,z))
    · have hh:=ht ha
      have hgap:0<(carrier L k).terminal (separated k (x,t,z))-q:=sub_pos.mpr ha.2
      have hp:(((carrier L k).terminal (separated k (x,t,z))-q)^(P.exponent/8-1))^2=
          ((carrier L k).terminal (separated k (x,t,z))-q)^(P.exponent/4-2):=by
        rw [←Real.rpow_mul_natCast hgap.le]
        congr 1
        ring
      have hsq:B t^2=ε^2*D*timeWeight L ell C k (separated k (x,t,z))^2*
          PastWordTimeFields.total L P k (separated k (x,t,z)) A0 ν*
            ((carrier L k).terminal (separated k (x,t,z))-q)^(P.exponent/4-2):=by
        dsimp only [B,A,activeTotal]
        rw [if_pos ha]
        simp only [mul_pow,Real.sq_sqrt hD,Real.sq_sqrt (PastWordTimeFields.total_nonneg _ _ _ _ _ _),hp]
        ring
      exact ⟨by simpa only [Real.norm_eq_abs] using hh.1,
        by simpa only [Real.norm_eq_abs,hsq] using hh.2⟩
    · have hfzero:=hz t ha
      simp only [hfzero,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),integral_zero]
      exact ⟨integrable_const (0:ℝ),sq_nonneg _⟩
  have hh:=HilbertParameterAverage.finite_energy μ old F hF B hBm hBi hBn
    (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨hh.1,by simpa only [Real.norm_eq_abs] using hh.2.1,?_⟩
  have he:(∫t,B t ∂old)^2=ε^2*D*(∫t,A t ∂old)^2:=by
    rw [show B=fun t=>(ε*sqrt D)*A t from rfl,integral_const_mul,mul_pow,mul_pow,Real.sq_sqrt hD]
  simpa only [Real.norm_eq_abs,he] using hh.2.2

end SHE.PastNewestTimeIntegral
