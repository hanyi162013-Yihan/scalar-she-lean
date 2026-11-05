module

public import SHE.PhysicalAssignmentTimeFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.PhysicalAssignmentGapScale
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure PhysicalOrderedGaps OrderedGapCoordinates GapSimplexReflection
open scoped BigOperators
open Classical
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

def activeIntegrand (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q fresh A0 ν : ℝ)
    (cs : List (Fin k×Fin (k+1))) (p : History X k) : ℝ :=
  if StrictHistory L k p ∧ q<(carrier L k).terminal p then
    ((carrier L k).terminal p-q)^(fresh-1)*
      (timeWeight L ell C k p*|SharpWordTimeScale.factor L Q k p q cs A0 ν|) else 0

theorem activeIntegrand_measurable (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q fresh A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) :
    Measurable (activeIntegrand L Q ell C k q fresh A0 ν cs) := by
  apply Measurable.ite (activeHistory_measurableSet L k q)
  · have hm : Measurable (fun p : History X k=>|SharpWordTimeScale.factor L Q k p q cs A0 ν|) := by
      simpa only [Real.norm_eq_abs] using (SharpWordTimeScale.factor_measurable L Q k q cs A0 ν).norm
    exact ((real_rpow_measurable _).comp ((carrier L k).terminal_measurable.sub_const q)).mul
      ((FixedHistoryTimeFactors.timeWeight_measurable L ell C k).mul
        hm)
  · exact measurable_const

theorem activeIntegrand_nonneg (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j)
    (k : ℕ) (q fresh A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) (p : History X k) :
    0≤activeIntegrand L Q ell C k q fresh A0 ν cs p := by
  unfold activeIntegrand
  split_ifs with h
  · exact mul_nonneg (Real.rpow_nonneg (sub_pos.mpr h.2).le _)
      (mul_nonneg (timeWeight_nonneg L hell C hC k p h.1) (abs_nonneg _))
  · exact le_rfl

/-- Literal physical assignment integration under the ORIGINAL old-time
product measure. Every fresh/old gap, rough-block minimum, root clip,
and empty full native age is retained before the proved scalar bound. -/
theorem actual_assignment_integral_bound (L : Level R X n)
    (Q : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ p,L.terminal p=T)
    {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j)
    (k : ℕ) (p : X) (x : Fin k→StoppedFourier.HeatCircle)
    {q fresh A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hf : 0<fresh) (hf1 : fresh≤1) (hA0 : 0≤A0) (hν : 0≤ν)
    (cs : List (Fin k×Fin (k+1))) (hc : cs∈assignments (m:=k+1) (List.finRange k)) :
    let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
    let K := scorePrefactor ell C k*prefactor Q cs A0 n*T^((Q.exponent/4)*(emptyCount cs:ℝ))
    Integrable (fun t=>activeIntegrand L Q ell C k q fresh A0 ν cs (separated k (p,t,x)))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,activeIntegrand L Q ell C k q fresh A0 ν cs (separated k (p,t,x))
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      K*((((k+1:ℕ):ℝ)^2/fresh*inverseDegreeProduct cs hc (Q.exponent/4))*
        (T-q)^(fresh+(Q.exponent/4)*(roughCount cs:ℝ)-1)*rootMass v (T-q)^(rootCount cs)) := by
  intro v K
  let μt := Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let F : (Fin k→ℝ)→ℝ := fun d=>(slack (T-q) d)^(fresh-1)*weight cs v (Q.exponent/4) d
  let G : (Fin k→ℝ)→ℝ := fun t=>if StrictHistory L k (separated k (p,t,x)) ∧
      q<(carrier L k).terminal (separated k (p,t,x)) then F (gaps T k t) else 0
  have hq0 : 0≤q := R.base_nonneg.trans hqbase
  have hT0 : 0≤T := hq0.trans hqT.le
  have ha : 0<Q.exponent/4 := div_pos Q.exponent_pos (by norm_num)
  have ha1 : Q.exponent/4≤1 := by linarith [Q.exponent_le_one]
  have hv : 0≤v := mul_nonneg hν (Real.sqrt_nonneg _)
  have hh := assignedDensity_integral_bound cs hc hv ha ha1 hf hf1 (sub_pos.mpr hqT)
  have he : (fun d : Fin k→ℝ=>if (∀ i,0<d i) ∧ (∑ i,d i)<T-q then F d else 0)=
      assignedDensity cs v (Q.exponent/4) fresh (T-q) := by
    funext d
    simp only [F,assignedDensity,GapSimplexFaces.simplex,slack,sub_pos]
  have hGi : Integrable G μt := by
    apply (active_gap_integrable_iff L T hT q hqbase hTH k p x F).mpr
    rw [he]
    exact hh.1
  have hGval : (∫ t,G t ∂μt)=∫ d,assignedDensity cs v (Q.exponent/4) fresh (T-q) d := by
    change (∫ t,if StrictHistory L k (separated k (p,t,x)) ∧
      q<(carrier L k).terminal (separated k (p,t,x)) then F (gaps T k t) else 0 ∂μt)=_
    rw [active_gap_integral L T hT q hqbase hTH,he]
  have hK : 0≤K := mul_nonneg
    (mul_nonneg (scorePrefactor_nonneg hell C hC k) (prefactor_nonneg Q cs hA0 n))
    (Real.rpow_nonneg hT0 _)
  have hdom (t : Fin k→ℝ) :
      activeIntegrand L Q ell C k q fresh A0 ν cs (separated k (p,t,x))≤K*G t := by
    by_cases ht : StrictHistory L k (separated k (p,t,x)) ∧ q<(carrier L k).terminal (separated k (p,t,x))
    · have hinit : initialTerminal L k (separated k (p,t,x))≤T := by
        simp only [initialTerminal,root_separated,hT,le_refl]
      have hb := physical_time_factor_bound L Q ell hell C hC k _ ht.1 hq0 ht.2 hT0 hinit hA0 hν cs hc
      have hgap := old_gaps_eq L T hT k t p x ht.1
      have hfresh : (carrier L k).terminal (separated k (p,t,x))-q=slack (T-q) (gaps T k t) := by
        rw [terminal_eq_boundary L T hT k t p x ht.1]
        simp only [slack,sum_gaps]
        ring
      dsimp only [activeIntegrand,G]
      rw [if_pos ht,if_pos ht]
      have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (sub_pos.mpr ht.2).le (fresh-1))
      rw [hgap,hfresh] at hm
      rw [hfresh]
      dsimp only [K,F,v] at hm ⊢
      convert! hm using 1 <;> ring
    · simp only [activeIntegrand,G,if_neg ht,mul_zero,le_refl]
  have hs : Measurable (fun t : Fin k→ℝ=>separated k (p,t,x)) :=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hin : Integrable (fun t=>activeIntegrand L Q ell C k q fresh A0 ν cs (separated k (p,t,x))) μt :=
    (hGi.const_mul K).mono' ((activeIntegrand_measurable L Q ell C k q fresh A0 ν cs).comp hs).aestronglyMeasurable
      (ae_of_all _ (fun t=>by rw [Real.norm_of_nonneg (activeIntegrand_nonneg L Q hell C hC k q fresh A0 ν cs _)];exact hdom t))
  refine ⟨hin,?_⟩
  calc
    _ ≤ ∫ t,K*G t ∂μt := integral_mono hin (hGi.const_mul K) hdom
    _ = K*(∫ d,assignedDensity cs v (Q.exponent/4) fresh (T-q) d) := by rw [integral_const_mul,hGval]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh.2 hK

end SHE.PhysicalAssignmentGapScale
