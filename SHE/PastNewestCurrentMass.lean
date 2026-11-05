module
public import SHE.PastNewestCurrentBudget

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.PastNewestTimeIntegral
open Set MeasureTheory Real GaussianAssignmentBlocks PhysicalAssignmentGapScale AllocatedAssignmentKernel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure CoveredHistoryGeometry
open scoped BigOperators
variable {X:Type}[MeasurableSpace X]{R:ReferenceData}{n:ℕ}(L:Level R X n)

def currentMass (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)
    (fresh A0 ν:ℝ)(x:X)(z:Fin k→StoppedFourier.HeatCircle)(q:ℝ):ℝ:=
  ∫t,activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z))
    ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))

theorem currentMass_measurable (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)(k:ℕ)
    (fresh A0 ν:ℝ)(x:X)(z:Fin k→StoppedFourier.HeatCircle):
    Measurable (currentMass L P ell C k fresh A0 ν x z):=by
  let h:(Fin k→ℝ)→History X k:=fun t=>separated k (x,t,z)
  have hh:Measurable h:=(separated_measurable k).comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hT:=((carrier L k).terminal_measurable.comp hh).comp (measurable_snd:Measurable (Prod.snd:ℝ×(Fin k→ℝ)→(Fin k→ℝ)))
  have hs:MeasurableSet {p:ℝ×(Fin k→ℝ)|StrictHistory L k (h p.2) ∧ p.1<(carrier L k).terminal (h p.2)}:=
    ((strictHistory_measurableSet L k).preimage (hh.comp measurable_snd)).inter
      (measurableSet_lt measurable_fst hT)
  have hm:Measurable (fun p:ℝ×(Fin k→ℝ)=>activeTotal L P ell C k p.1 fresh A0 ν (h p.2)):=by
    apply Measurable.ite hs _ measurable_const
    exact ((((real_rpow_measurable _).comp (hT.sub measurable_fst)).mul
      ((FixedHistoryTimeFactors.timeWeight_measurable L ell C k).comp (hh.comp measurable_snd))).mul
        (Real.continuous_sqrt.measurable.comp
          ((PastWordTimeFields.total_measurable L P k A0 ν).comp (hh.comp measurable_snd))))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Current time is integrated in RMS, rather than squaring its singular
fresh kernel first. This integral includes all current/fresh collisions. -/
theorem currentMass_integrable (P:CanonicalCovariance.ProfileParameters)(T:ℝ)(hT:∀x,L.terminal x=T)
    {ell:ℝ}(hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(x:X)(z:Fin k→StoppedFourier.HeatCircle)
    {fresh A0 ν:ℝ}(hbase:R.base<T)(hTH:T≤R.horizon)(hf:0<fresh)(hf1:fresh≤1)(hA:0≤A0)(hν:0≤ν):
    Integrable (currentMass L P ell C k fresh A0 ν x z) (volume.restrict (Ioc R.base T)) ∧
      (∫q,currentMass L P ell C k fresh A0 ν x z q ∂volume.restrict (Ioc R.base T))≤
        currentConstant P ell C n k (T-R.base) fresh A0 ν*(T-R.base)^fresh/fresh:=by
  let K:=currentConstant P ell C n k (T-R.base) fresh A0 ν
  have hb:=current_bound L P T hT hell C hC k x z hbase hTH hf hf1 hA hν
  have hK:0≤K:=hb.1
  have hi0:IntervalIntegrable (fun s:ℝ=>s^(fresh-1)) volume 0 (T-R.base):=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi:IntervalIntegrable (fun q:ℝ=>(T-q)^(fresh-1)) volume R.base T:=by
    simpa only [sub_self,sub_sub_cancel,sub_zero] using (hi0.comp_sub_left T).symm
  have hki:Integrable (fun q:ℝ=>(T-q)^(fresh-1)) (volume.restrict (Ioc R.base T)):=by
    simpa only [uIoc_of_le hbase.le,IntegrableOn] using hi.def'
  have hm:=currentMass_measurable L P ell C k fresh A0 ν x z
  have hn(q:ℝ):0≤currentMass L P ell C k fresh A0 ν x z q:=by
    apply integral_nonneg
    intro t
    unfold activeTotal
    dsimp only
    split_ifs with ht
    · exact mul_nonneg (mul_nonneg (rpow_nonneg (sub_pos.mpr ht.2).le _)
        (timeWeight_nonneg L hell C hC k _ ht.1)) (sqrt_nonneg _)
    · exact le_rfl
  have hbound:∀ᵐq∂volume.restrict (Ioc R.base T),currentMass L P ell C k fresh A0 ν x z q≤K*(T-q)^(fresh-1):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne T)] with q hq hne
    exact hb.2 q hq.1.le (lt_of_le_of_ne hq.2 hne)
  have hmi:Integrable (currentMass L P ell C k fresh A0 ν x z) (volume.restrict (Ioc R.base T)):=
    (hki.const_mul K).mono' hm.aestronglyMeasurable
      (hbound.mono (fun q h=>by rw [Real.norm_of_nonneg (hn q)];exact h))
  have he:(∫q,(T-q)^(fresh-1) ∂volume.restrict (Ioc R.base T))=(T-R.base)^fresh/fresh:=by
    rw [←intervalIntegral.integral_of_le hbase.le,
      intervalIntegral.integral_comp_sub_left (fun s:ℝ=>s^(fresh-1)) T,sub_self,
      integral_rpow (Or.inl (by linarith:-1<fresh-1)),show fresh-1+1=fresh by ring,
      Real.zero_rpow hf.ne',sub_zero]
  refine ⟨hmi,(integral_mono_ae hmi (hki.const_mul K) hbound).trans_eq ?_⟩
  rw [integral_const_mul,he]
  dsimp only [K]
  ring

end SHE.PastNewestTimeIntegral
