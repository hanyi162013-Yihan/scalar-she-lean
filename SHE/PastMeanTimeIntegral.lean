module

public import SHE.PastMeanTimeFactors
public import SHE.QuarterRMSOldTime

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure PhysicalOrderedGaps OrderedGapCoordinates GapSimplexReflection
  PhysicalAssignmentGapScale
open scoped BigOperators
open Classical
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- The actual relative-age assignment density is integrated under the
original absolute old-time measure. Every full native age is bounded by
T-base, while the remaining integration width is the true T-q. -/
theorem assignment_old_time_bound (P : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ x,L.terminal x=T) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ) (x : X) (z : Fin k→StoppedFourier.HeatCircle)
    {q fresh A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hf : 0<fresh) (hf1 : fresh≤1) (hA0 : 0≤A0) (hν : 0≤ν)
    (cs : List (Fin k×Fin (k+1))) (hc : cs∈assignments (m:=k+1) (List.finRange k)) :
    let v0:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
    let K:=scorePrefactor ell C k*prefactor P cs A0 n*(T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ))
    Integrable (fun t=>activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z)))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
      (∫ t,activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z))
        ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
        K*((((k+1:ℕ):ℝ)^2/fresh*inverseDegreeProduct cs hc (P.exponent/4))*
          (T-q)^(fresh+(P.exponent/4)*(roughCount cs:ℝ)-1)*rootMass v0 (T-q)^(rootCount cs)) := by
  intro v0 K
  let μt:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let F : (Fin k→ℝ)→ℝ:=fun d=>(slack (T-q) d)^(fresh-1)*weight cs v0 (P.exponent/4) d
  let G : (Fin k→ℝ)→ℝ:=fun t=>if StrictHistory L k (separated k (x,t,z)) ∧
      q<(carrier L k).terminal (separated k (x,t,z)) then F (gaps T k t) else 0
  have hspan : 0≤T-R.base:=sub_nonneg.mpr (hqbase.trans hqT.le)
  have ha : 0<P.exponent/4:=div_pos P.exponent_pos (by norm_num)
  have ha1 : P.exponent/4≤1:=by linarith [P.exponent_le_one]
  have hv : 0≤v0:=mul_nonneg hν (sqrt_nonneg _)
  have hh:=assignedDensity_integral_bound cs hc hv ha ha1 hf hf1 (sub_pos.mpr hqT)
  have he : (fun d : Fin k→ℝ=>if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0)=
      assignedDensity cs v0 (P.exponent/4) fresh (T-q) := by
    funext d
    simp only [F,assignedDensity,GapSimplexFaces.simplex,slack,sub_pos]
  have hGi : Integrable G μt := by
    apply (active_gap_integrable_iff L T hT q hqbase hTH k x z F).mpr
    rw [he]
    exact hh.1
  have hGval : (∫ t,G t ∂μt)=∫ d,assignedDensity cs v0 (P.exponent/4) fresh (T-q) d := by
    change (∫ t,if StrictHistory L k (separated k (x,t,z)) ∧
      q<(carrier L k).terminal (separated k (x,t,z)) then F (gaps T k t) else 0 ∂μt)=_
    rw [active_gap_integral L T hT q hqbase hTH,he]
  have hK : 0≤K:=mul_nonneg
    (mul_nonneg (scorePrefactor_nonneg hell C hC k) (prefactor_nonneg P cs hA0 n)) (rpow_nonneg hspan _)
  have hdom (t : Fin k→ℝ) : activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z))≤K*G t := by
    by_cases ht : StrictHistory L k (separated k (x,t,z)) ∧ q<(carrier L k).terminal (separated k (x,t,z))
    · have hinit : initialTerminal L k (separated k (x,t,z))≤T := by
        simp only [initialTerminal,root_separated,hT,le_refl]
      have hb:=time_factor_bound L P hell C hC k _ ht.1 hqbase ht.2 hinit hA0 hν cs hc
      have hgap:=old_gaps_eq L T hT k t x z ht.1
      have hfresh : (carrier L k).terminal (separated k (x,t,z))-q=slack (T-q) (gaps T k t) := by
        rw [terminal_eq_boundary L T hT k t x z ht.1]
        simp only [slack,sum_gaps]
        ring
      dsimp only [activeFactor,G]
      rw [if_pos ht,if_pos ht]
      have hm:=mul_le_mul_of_nonneg_left hb (rpow_nonneg (sub_pos.mpr ht.2).le (fresh-1))
      rw [hgap,hfresh] at hm
      rw [hfresh]
      dsimp only [K,F,v0] at hm ⊢
      convert! hm using 1 <;> ring
    · simp only [activeFactor,G,if_neg ht,mul_zero,le_refl]
  have hs : Measurable (fun t : Fin k→ℝ=>separated k (x,t,z)):=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hi : Integrable (fun t=>activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z))) μt :=
    (hGi.const_mul K).mono' ((activeFactor_measurable L P ell C k q fresh A0 ν cs).comp hs).aestronglyMeasurable
      (ae_of_all _ (fun t=>by
        rw [Real.norm_of_nonneg (activeFactor_nonneg L P hell C hC k q fresh A0 ν cs _)]
        exact hdom t))
  refine ⟨hi,?_⟩
  calc
    _≤∫ t,K*G t ∂μt:=integral_mono hi (hGi.const_mul K) hdom
    _=K*(∫ d,assignedDensity cs v0 (P.exponent/4) fresh (T-q) d):=by rw [integral_const_mul,hGval]
    _≤_:=mul_le_mul_of_nonneg_left hh.2 hK

/-- Exact local-span finite assignment budget, including depth zero.
Its shape is the checked universal ledger at relative T and q. -/
theorem old_time_budget (L : Level R StoppedFourier.HeatCircle 1)
    (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ x,L.terminal x=T)
    {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ)
    {q fresh A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hf : 0<fresh) (hf1 : fresh≤1) (hA0 : 0≤A0) (hν : 0≤ν) :
    Integrable (fun t=>totalIntegrand L P ell C k q fresh A0 ν (QuarterSpatialEvent.anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
      (∫ t,totalIntegrand L P ell C k q fresh A0 ν (QuarterSpatialEvent.anchor k t)
        ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
        QuarterRMSTimeFactors.oldTimeBudget P ell C k (T-R.base) (q-R.base) fresh A0 ν := by
  let cs:=assignments (m:=k+1) (List.finRange k)
  let μt:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  have hh (i : Fin cs.length):=assignment_old_time_bound L P T hT hell C hC k
    (0:StoppedFourier.HeatCircle) (fun _=>0) hqbase hqT hTH hf hf1 hA0 hν (cs.get i) (List.get_mem cs i)
  have hi:=integrable_finsetSum Finset.univ (fun i _=>(hh i).1)
  have he : (fun t=>totalIntegrand L P ell C k q fresh A0 ν (QuarterSpatialEvent.anchor k t))=
      fun t=>∑ i : Fin cs.length,activeFactor L P ell C k q fresh A0 ν (cs.get i) (QuarterSpatialEvent.anchor k t) := by
    funext t
    exact totalIntegrand_eq_sum L P ell C k q fresh A0 ν _
  refine ⟨by rw [he];simpa only [QuarterSpatialEvent.anchor] using hi,?_⟩
  rw [he]
  simp only [QuarterSpatialEvent.anchor]
  rw [integral_finsetSum _ (fun i _=>(hh i).1)]
  have hsum:=Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin cs.length)))=>(hh i).2)
  simpa only [QuarterRMSTimeFactors.oldTimeBudget,show T-R.base-(q-R.base)=T-q from by ring,QuarterSpatialEvent.anchor] using hsum

end SHE.PastMeanTimeFactors
