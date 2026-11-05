module
public import SHE.PastNewestTimeIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.PastNewestTimeIntegral
open Set MeasureTheory Real GaussianAssignmentBlocks PhysicalAssignmentGapScale AllocatedAssignmentKernel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure CoveredHistoryGeometry
open scoped BigOperators
open Classical
variable {X:Type}[MeasurableSpace X]{R:ReferenceData}{n:ℕ}(L:Level R X n)

def activeTotal (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(q fresh A0 ν:ℝ)(h:History X k):ℝ:=
  if StrictHistory L k h ∧ q<(carrier L k).terminal h then
    ((carrier L k).terminal h-q)^(fresh-1)*timeWeight L ell C k h*
      sqrt (PastWordTimeFields.total L P k h A0 ν) else 0

theorem activeTotal_measurable (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(q fresh A0 ν:ℝ):Measurable (activeTotal L P ell C k q fresh A0 ν):=by
  apply Measurable.ite (activeHistory_measurableSet L k q) _ measurable_const
  exact ((((real_rpow_measurable _).comp ((carrier L k).terminal_measurable.sub_const q)).mul
    (FixedHistoryTimeFactors.timeWeight_measurable L ell C k)).mul
      (Real.continuous_sqrt.measurable.comp (PastWordTimeFields.total_measurable L P k A0 ν)))

theorem sqrt_total_le_sum (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(h:History X k)(A0 ν:ℝ):
    sqrt (PastWordTimeFields.total L P k h A0 ν)≤
      ∑i:Fin (assignments (m:=k+1) (List.finRange k)).length,
        sqrt |PastMeanTimeFactors.factor L P k h ((assignments (m:=k+1) (List.finRange k)).get i) A0 ν|:=by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let f:Fin cs.length→ℝ:=fun i=>|PastMeanTimeFactors.factor L P k h (cs.get i) A0 ν|
  have he:PastWordTimeFields.total L P k h A0 ν=∑i:Fin cs.length,f i:=by
    simp only [PastWordTimeFields.total,MixedPastWordMoments.total,FiniteAssignmentMoments.map_sum_eq_fin]
    rfl
  rw [he]
  apply (Real.sqrt_le_left (Finset.sum_nonneg (fun _ _=>sqrt_nonneg _))).mpr
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (f:=fun i:Fin cs.length=>sqrt (f i))
    (fun _ _=>sqrt_nonneg _)
  have hfn(i:Fin cs.length):0≤f i:=abs_nonneg _
  simpa only [Real.sq_sqrt (hfn _)] using hh

theorem actual_total_integral_bound (P:CanonicalCovariance.ProfileParameters)
    (T:ℝ)(hT:∀x,L.terminal x=T){ell:ℝ}(hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)
    (k:ℕ)(x:X)(z:Fin k→StoppedFourier.HeatCircle){q fresh A0 ν:ℝ}
    (hqb:R.base≤q)(hqT:q<T)(hTH:T≤R.horizon)(hf:0<fresh)(hf1:fresh≤1)
    (hA:0≤A0)(hν:0≤ν):
    let cs:=assignments (m:=k+1) (List.finRange k)
    let w:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
    let p:=fun i:Fin cs.length=>Fin.cons fresh (fun j=>holderDegree (cs.get i) (List.get_mem cs i) (P.exponent/4) j/2)
    Integrable (fun t=>activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z)))
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫t,activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z))
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      ∑i:Fin cs.length,
        (scorePrefactor ell C k*sqrt (prefactor P (cs.get i) A0 n*
          (T-R.base)^((P.exponent/4)*(emptyCount (cs.get i):ℝ))))*
            (max 1 w)^((k:ℝ)/2)*(((k+1:ℕ):ℝ)^2/(T-q)*∏j,(T-q)^((p i) j)/((p i) j)):=by
  intro cs w p
  let μt:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  have hb(i:Fin cs.length):=actual_assignment_integral_bound L P T hT hell C hC k x z
    hqb hqT hTH hf hf1 hA hν (cs.get i) (List.get_mem cs i)
  have hsum:Integrable (fun t=>∑i:Fin cs.length,activeFactor L P ell C k q fresh A0 ν (cs.get i)
      (separated k (x,t,z))) μt:=integrable_finsetSum _ (fun i _=>(hb i).1)
  have hdom(t:Fin k→ℝ):activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z))≤
      ∑i:Fin cs.length,activeFactor L P ell C k q fresh A0 ν (cs.get i) (separated k (x,t,z)):=by
    by_cases ht:StrictHistory L k (separated k (x,t,z)) ∧ q<(carrier L k).terminal (separated k (x,t,z))
    · simp only [activeTotal,activeFactor,if_pos ht,←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sqrt_total_le_sum L P k _ A0 ν)
        (mul_nonneg (rpow_nonneg (sub_pos.mpr ht.2).le _) (timeWeight_nonneg L hell C hC k _ ht.1))
    · simp only [activeTotal,activeFactor,if_neg ht,Finset.sum_const_zero,le_refl]
  have hn(t:Fin k→ℝ):0≤activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z)):=by
    unfold activeTotal
    split_ifs with ht
    · exact mul_nonneg (mul_nonneg (rpow_nonneg (sub_pos.mpr ht.2).le _)
        (timeWeight_nonneg L hell C hC k _ ht.1)) (sqrt_nonneg _)
    · exact le_rfl
  have hs:Measurable (fun t:Fin k→ℝ=>separated k (x,t,z)):=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hi:Integrable (fun t=>activeTotal L P ell C k q fresh A0 ν (separated k (x,t,z))) μt:=
    hsum.mono' ((activeTotal_measurable L P ell C k q fresh A0 ν).comp hs).aestronglyMeasurable
      (ae_of_all _ (fun t=>by rw [Real.norm_of_nonneg (hn t)];exact hdom t))
  refine ⟨hi,?_⟩
  have hh:=integral_mono hi hsum hdom
  rw [integral_finsetSum _ (fun i _=>(hb i).1)] at hh
  exact hh.trans (Finset.sum_le_sum (fun i _=>by simpa only [w,p] using (hb i).2))

end SHE.PastNewestTimeIntegral
