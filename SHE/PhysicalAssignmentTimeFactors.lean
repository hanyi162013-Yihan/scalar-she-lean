module

public import SHE.PhysicalAssignmentGapScale
public import SHE.PhysicalGapIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalAssignmentGapScale
open Set MeasureTheory Real GaussianAssignmentBlocks GaussianFreshAssignments
  AssignmentGapPartition AllocatedAssignmentKernel CoveredHistoryGeometry CoveredControlledLaw
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain
open scoped BigOperators
open Classical
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}

def scorePrefactor (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) : ℝ := ∏ j : Fin k,C j/ell

def emptyCount {k m : ℕ} (cs : List (Fin k×Fin (m+1))) : ℕ :=
  (Finset.univ.filter (fun j : Fin m=>block cs j.succ=[])).card

theorem scorePrefactor_nonneg {ell : ℝ} (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ) :
    0≤scorePrefactor ell C k := Finset.prod_nonneg (fun j _=>div_nonneg (hC _) hell.le)

theorem timeWeight_eq (L : Level R X n) (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (p : History X k) :
    timeWeight L ell C k p=scorePrefactor ell C k*
      ∏ j,(upper L k p j-lower L k p j)⁻¹ := by
  induction k with
  | zero => simp only [timeWeight,scorePrefactor,Fin.prod_univ_zero,mul_one]
  | succ k ih =>
    rw [timeWeight,ih]
    unfold scorePrefactor
    rw [Fin.prod_univ_castSucc,Fin.prod_univ_succ]
    simp only [Fin.val_castSucc,Fin.val_last,upper,lower,Fin.cases_zero,Fin.cases_succ]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

theorem leaf_ages_bounds (L : Level R X n) (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q T : ℝ} (hq0 : 0≤q) (hq : q<(carrier L k).terminal p) (hT : initialTerminal L k p≤T) :
    ∀ j : Fin k,0≤targets L k p (leafIndex k (fun i=>i) j) ∧
      targets L k p (leafIndex k (fun i=>i) j)≤T := by
  intro j
  have he : targets L k p (leafIndex k (fun i=>i) j)=lower L k p j := by
    unfold targets
    rw [leaf_observation]
  rw [he]
  exact ⟨hq0.trans (hq.le.trans (terminal_le_lower L k p j)),
    (lower_lt_upper L k p hp j).le.trans ((upper_le_initial L k p j).trans hT)⟩

theorem physical_factor_nonneg (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q A0 ν : ℝ} (hq0 : 0≤q) (hq : q<(carrier L k).terminal p)
    (hA0 : 0≤A0) (hν : 0≤ν) (cs : List (Fin k×Fin (k+1))) :
    0≤SharpWordTimeScale.factor L Q k p q cs A0 ν := by
  rw [physical_factor_eq]
  apply mul_nonneg
  · apply mul_nonneg (prefactor_nonneg Q cs hA0 n)
    apply Finset.prod_nonneg
    intro l _
    exact gainBlock_nonneg cs (mul_nonneg hν (Real.sqrt_nonneg _)) _ _
      (fun j=>(sub_pos.mpr (lower_lt_upper L k p hp j)).le) l
  · apply Finset.prod_nonneg
    intro j _
    split_ifs
    · exact Real.rpow_nonneg
        ((leaf_ages_bounds L k p hp hq0 hq (le_refl (initialTerminal L k p)) j).1) _
    · exact zero_le_one

/-- Exact physical denominators and sharp assignment gains are factored
before the time estimate. Empty leaves keep their full native age. -/
theorem physical_time_factor_bound (L : Level R X n) (Q : CanonicalCovariance.ProfileParameters)
    (ell : ℝ) (hell : 0<ell) (C : ℕ→ℝ) (hC : ∀ j,0≤C j)
    (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q T A0 ν : ℝ} (hq0 : 0≤q) (hq : q<(carrier L k).terminal p)
    (hT0 : 0≤T) (hT : initialTerminal L k p≤T) (hA0 : 0≤A0) (hν : 0≤ν)
    (cs : List (Fin k×Fin (k+1))) (hc : cs∈assignments (m:=k+1) (List.finRange k)) :
    timeWeight L ell C k p*|SharpWordTimeScale.factor L Q k p q cs A0 ν|≤
      (scorePrefactor ell C k*prefactor Q cs A0 n*T^((Q.exponent/4)*(emptyCount cs:ℝ)))*
        weight cs (ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))) (Q.exponent/4)
          (fun j=>upper L k p j-lower L k p j) := by
  rw [abs_of_nonneg (physical_factor_nonneg L Q k p hp hq0 hq hA0 hν cs),
    timeWeight_eq,physical_factor_eq]
  let d : Fin k→ℝ := fun j=>upper L k p j-lower L k p j
  let age : Fin k→ℝ := fun j=>targets L k p (leafIndex k (fun i=>i) j)
  let v := ν*sqrt (ProfileVariance.upperConstant*(Q.lower/2))
  have he := inverse_mul_gain_eq_weight cs hc v (Q.exponent/4) d
  have hbound := emptyGain_bound cs (a:=Q.exponent/4) (T:=T)
    (div_nonneg Q.exponent_pos.le (by norm_num)) hT0 age
    (leaf_ages_bounds L k p hp hq0 hq hT)
  have hbase : 0≤scorePrefactor ell C k*prefactor Q cs A0 n*weight cs v (Q.exponent/4) d := by
    exact mul_nonneg (mul_nonneg (scorePrefactor_nonneg hell C hC k) (prefactor_nonneg Q cs hA0 n))
      (Finset.prod_nonneg (fun l _=>blockWeight_nonneg cs (mul_nonneg hν (Real.sqrt_nonneg _)) d
        (fun j=>sub_pos.mpr (lower_lt_upper L k p hp j)) l))
  have hh := mul_le_mul_of_nonneg_left hbound hbase
  change _≤_
  calc
    _ = (scorePrefactor ell C k*prefactor Q cs A0 n*weight cs v (Q.exponent/4) d)*
        emptyGain cs (Q.exponent/4) age := by rw [←he];ring
    _ ≤ _ := by convert! hh using 1 <;> unfold emptyCount <;> ring

end SHE.PhysicalAssignmentGapScale
