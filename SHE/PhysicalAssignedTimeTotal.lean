module

public import SHE.PhysicalAssignedTimeIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.PhysicalAssignmentGapScale
open Set MeasureTheory Real GaussianAssignmentBlocks AllocatedAssignmentKernel CoveredHistoryGeometry
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure
open scoped BigOperators
open Classical
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

def totalIntegrand (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q fresh A0 ν : ℝ) (p : History X k) : ℝ :=
  if StrictHistory L k p ∧ q<(carrier L k).terminal p then
    ((carrier L k).terminal p-q)^(fresh-1)*
      (timeWeight L ell C k p*SharpWordTimeScale.total L Q k p q A0 ν) else 0

theorem totalIntegrand_eq_sum (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (q fresh A0 ν : ℝ) (p : History X k) :
    totalIntegrand L Q ell C k q fresh A0 ν p=
      ∑ i : Fin (assignments (m:=k+1) (List.finRange k)).length,
        activeIntegrand L Q ell C k q fresh A0 ν
          ((assignments (m:=k+1) (List.finRange k)).get i) p := by
  by_cases hp : StrictHistory L k p ∧ q<(carrier L k).terminal p
  · simp only [totalIntegrand,activeIntegrand,if_pos hp,SharpWordTimeScale.total]
    rw [FiniteAssignmentMoments.map_sum_eq_fin]
    rw [Finset.mul_sum,Finset.mul_sum]
  · simp only [totalIntegrand,activeIntegrand,if_neg hp,Finset.sum_const_zero]

theorem empty_rough_count {k m : ℕ} (cs : List (Fin k×Fin (m+1))) :
    emptyCount cs+roughCount cs=m := by
  have hr : roughCount cs=(Finset.univ.filter (fun j : Fin m=>block cs j.succ≠[])).card := by
    unfold roughCount
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_succ]
    simp only [ne_eq,not_true_eq_false,false_and,ite_false,Fin.succ_ne_zero,not_false_eq_true,true_and,zero_add]
  rw [hr]
  unfold emptyCount
  have hh := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (p:=fun j : Fin m=>block cs j.succ=[])
  simpa only [Finset.card_univ,Fintype.card_fin] using hh

/-- The complete actual finite assignment sum is time integrable, with
each individual block/root degree preserved in the finite bound. -/
theorem actual_total_integral_bound (L : Level R X n)
    (Q : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ p,L.terminal p=T)
    {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j)
    (k : ℕ) (p : X) (x : Fin k→StoppedFourier.HeatCircle)
    {q fresh A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hf : 0<fresh) (hf1 : fresh≤1) (hA0 : 0≤A0) (hν : 0≤ν) :
    let cs := assignments (m:=k+1) (List.finRange k)
    let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
    Integrable (fun t=>totalIntegrand L Q ell C k q fresh A0 ν (separated k (p,t,x)))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,totalIntegrand L Q ell C k q fresh A0 ν (separated k (p,t,x))
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      ∑ i : Fin cs.length,
        (scorePrefactor ell C k*prefactor Q (cs.get i) A0 n*T^((Q.exponent/4)*(emptyCount (cs.get i):ℝ)))*
        (((((k+1:ℕ):ℝ)^2/fresh)*inverseDegreeProduct (cs.get i) (List.get_mem cs i) (Q.exponent/4))*
          (T-q)^(fresh+(Q.exponent/4)*(roughCount (cs.get i):ℝ)-1)*rootMass v (T-q)^(rootCount (cs.get i))) := by
  intro cs v
  let μt := Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  have hh (i : Fin cs.length) := actual_assignment_integral_bound L Q T hT hell C hC k p x
    hqbase hqT hTH hf hf1 hA0 hν (cs.get i) (List.get_mem cs i)
  have hi := integrable_finsetSum Finset.univ (fun i _=>(hh i).1)
  have he : (fun t=>totalIntegrand L Q ell C k q fresh A0 ν (separated k (p,t,x)))=
      fun t=>∑ i : Fin cs.length,activeIntegrand L Q ell C k q fresh A0 ν (cs.get i) (separated k (p,t,x)) := by
    funext t
    exact totalIntegrand_eq_sum L Q ell C k q fresh A0 ν _
  refine ⟨by rwa [he],?_⟩
  rw [he,integral_finsetSum _ (fun i _=>(hh i).1)]
  exact Finset.sum_le_sum (fun i _=>(hh i).2)

end SHE.PhysicalAssignmentGapScale
