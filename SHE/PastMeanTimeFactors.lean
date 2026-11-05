module

public import SHE.ConditionalGapFactors
public import SHE.PastWordTimeFields
public import SHE.PhysicalAssignedTimeTotal
public import SHE.QuarterRMSFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set Filter MeasureTheory Real GaussianAssignmentBlocks GaussianFreshAssignments
  AssignmentGapPartition AllocatedAssignmentKernel PhysicalAssignmentGapScale
  CoveredHistoryGeometry CoveredControlledLaw CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain
open scoped BigOperators
open Classical
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

def factor (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) : ℝ :=
  MixedPastWordMoments.factor (d:=n) P (fun j=>lower L k p j-R.base)
    (fun j=>upper L k p j-R.base) (fun j=>targets L k p (leafIndex k (fun i=>i) j)-R.base) cs A0 ν

theorem factor_eq_allocated (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) :
    factor L P k p cs A0 ν=prefactor P cs A0 n*
      gain cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (P.exponent/4)
        (fun j=>upper L k p j-lower L k p j)*
      emptyGain cs (P.exponent/4) (fun j=>targets L k p (leafIndex k (fun i=>i) j)-R.base) := by
  unfold factor
  rw [MixedPastWordMoments.factor_eq_allocated_gain]
  have he : (fun j : Fin k=>upper L k p j-R.base-(lower L k p j-R.base))=
      (fun j=>upper L k p j-lower L k p j) := by funext j;ring
  rw [he]

theorem factor_measurable (P : CanonicalCovariance.ProfileParameters) (k : ℕ)
    (cs : List (Fin k×Fin (k+1))) (A0 ν : ℝ) :
    Measurable (fun p=>factor L P k p cs A0 ν) :=
  MixedPastWordMoments.factor_measurable P _ _ _
    (fun j=>(lower_measurable L k j).sub_const R.base)
    (fun j=>(upper_measurable L k j).sub_const R.base)
    (fun _=>((carrier L k).observations.target_measurable _).sub_const R.base) cs A0 ν n

/-- Empty rough blocks have their genuine local observation age. -/
theorem relative_ages_bounds (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q T : ℝ} (hqbase : R.base≤q) (hq : q<(carrier L k).terminal p)
    (hT : initialTerminal L k p≤T) :
    ∀ j : Fin k,0≤targets L k p (leafIndex k (fun i=>i) j)-R.base ∧
      targets L k p (leafIndex k (fun i=>i) j)-R.base≤T-R.base := by
  intro j
  have he : targets L k p (leafIndex k (fun i=>i) j)=lower L k p j := by
    unfold targets
    rw [leaf_observation]
  rw [he]
  exact ⟨sub_nonneg.mpr (hqbase.trans (hq.le.trans (terminal_le_lower L k p j))),
    sub_le_sub_right ((lower_lt_upper L k p hp j).le.trans ((upper_le_initial L k p j).trans hT)) _⟩

theorem factor_nonneg (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (p : History X k)
    (hp : StrictHistory L k p) {q A0 ν : ℝ} (hqbase : R.base≤q)
    (hq : q<(carrier L k).terminal p) (hA0 : 0≤A0) (hν : 0≤ν)
    (cs : List (Fin k×Fin (k+1))) : 0≤factor L P k p cs A0 ν := by
  rw [factor_eq_allocated]
  apply mul_nonneg
  · exact mul_nonneg (prefactor_nonneg P cs hA0 n)
      (Finset.prod_nonneg (fun l _=>gainBlock_nonneg cs (mul_nonneg hν (sqrt_nonneg _)) _ _
        (fun j=>(sub_pos.mpr (lower_lt_upper L k p hp j)).le) l))
  · apply Finset.prod_nonneg
    intro j _
    split_ifs
    · exact rpow_nonneg ((relative_ages_bounds L k p hp hqbase hq (le_refl _) j).1) _
    · exact zero_le_one

/-- True old denominators and local ages feed the same allocated-gap
ledger. Its full-age factor is T-base, even when T is an absolute time. -/
theorem time_factor_bound (P : CanonicalCovariance.ProfileParameters) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q T A0 ν : ℝ} (hqbase : R.base≤q) (hq : q<(carrier L k).terminal p)
    (hT : initialTerminal L k p≤T) (hA0 : 0≤A0) (hν : 0≤ν)
    (cs : List (Fin k×Fin (k+1))) (hc : cs∈assignments (m:=k+1) (List.finRange k)) :
    timeWeight L ell C k p*|factor L P k p cs A0 ν|≤
      (scorePrefactor ell C k*prefactor P cs A0 n*(T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ)))*
        weight cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))) (P.exponent/4)
          (fun j=>upper L k p j-lower L k p j) := by
  rw [abs_of_nonneg (factor_nonneg L P k p hp hqbase hq hA0 hν cs),timeWeight_eq,factor_eq_allocated]
  let d : Fin k→ℝ:=fun j=>upper L k p j-lower L k p j
  let age : Fin k→ℝ:=fun j=>targets L k p (leafIndex k (fun i=>i) j)-R.base
  let v0:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
  have he:=inverse_mul_gain_eq_weight cs hc v0 (P.exponent/4) d
  have hspan : 0≤T-R.base := sub_nonneg.mpr (hqbase.trans (hq.le.trans ((terminal_le_initial L k p).trans hT)))
  have hbound:=emptyGain_bound cs (a:=P.exponent/4) (T:=T-R.base)
    (div_nonneg P.exponent_pos.le (by norm_num)) hspan age
    (relative_ages_bounds L k p hp hqbase hq hT)
  have hbase : 0≤scorePrefactor ell C k*prefactor P cs A0 n*weight cs v0 (P.exponent/4) d :=
    mul_nonneg (mul_nonneg (scorePrefactor_nonneg hell C hC k) (prefactor_nonneg P cs hA0 n))
      (Finset.prod_nonneg (fun l _=>blockWeight_nonneg cs (mul_nonneg hν (sqrt_nonneg _)) d
        (fun j=>sub_pos.mpr (lower_lt_upper L k p hp j)) l))
  have hh:=mul_le_mul_of_nonneg_left hbound hbase
  calc
    _=(scorePrefactor ell C k*prefactor P cs A0 n*weight cs v0 (P.exponent/4) d)*emptyGain cs (P.exponent/4) age := by
      rw [←he]
      ring
    _≤_ := by convert! hh using 1 <;> unfold emptyCount <;> ring

def activeFactor (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) (p : History X k) : ℝ :=
  if StrictHistory L k p ∧ q<(carrier L k).terminal p then
    ((carrier L k).terminal p-q)^(fresh-1)*(timeWeight L ell C k p*|factor L P k p cs A0 ν|) else 0

def totalIntegrand (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) (p : History X k) : ℝ :=
  if StrictHistory L k p ∧ q<(carrier L k).terminal p then
    ((carrier L k).terminal p-q)^(fresh-1)*(timeWeight L ell C k p*PastWordTimeFields.total L P k p A0 ν) else 0

theorem activeFactor_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) :
    Measurable (activeFactor L P ell C k q fresh A0 ν cs) :=
  ((((carrier L k).terminal_measurable.sub_const q).pow_const _).mul
    ((FixedHistoryTimeFactors.timeWeight_measurable L ell C k).mul
      (continuous_abs.measurable.comp (factor_measurable L P k cs A0 ν)))).ite
        (activeHistory_measurableSet L k q) measurable_const

theorem activeFactor_nonneg (P : CanonicalCovariance.ProfileParameters) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ) (q fresh A0 ν : ℝ)
    (cs : List (Fin k×Fin (k+1))) (p : History X k) : 0≤activeFactor L P ell C k q fresh A0 ν cs p := by
  unfold activeFactor
  split_ifs with h
  · exact mul_nonneg (rpow_nonneg (sub_pos.mpr h.2).le _)
      (mul_nonneg (timeWeight_nonneg L hell C hC k p h.1) (abs_nonneg _))
  · exact le_rfl

theorem totalIntegrand_eq_sum (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) (p : History X k) :
    totalIntegrand L P ell C k q fresh A0 ν p=
      ∑ i : Fin (assignments (m:=k+1) (List.finRange k)).length,
        activeFactor L P ell C k q fresh A0 ν ((assignments (m:=k+1) (List.finRange k)).get i) p := by
  by_cases hp : StrictHistory L k p ∧ q<(carrier L k).terminal p
  · simp only [totalIntegrand,activeFactor,if_pos hp,PastWordTimeFields.total,MixedPastWordMoments.total]
    rw [FiniteAssignmentMoments.map_sum_eq_fin,Finset.mul_sum,Finset.mul_sum]
    rfl
  · simp only [totalIntegrand,activeFactor,if_neg hp,Finset.sum_const_zero]

end SHE.PastMeanTimeFactors
