module

public import SHE.VectorControlledAssignedWord
public import SHE.VectorPairedJointRoot
public import SHE.PairedRoughBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.AssignedCurrentTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianAudit
open scoped BigOperators

def terms {I : Type*} (a b : I→ℝ) : List I→List ℝ
  | [] => []
  | i::is => ((a i-b i)*(is.map a).prod)::((terms a b is).map (fun t => b i*t))

theorem terms_sum {I : Type*} (a b : I→ℝ) (is : List I) :
    (terms a b is).sum=(is.map a).prod-(is.map b).prod := by
  induction is with
  | nil => simp [terms]
  | cons i is ih =>
    have hid (l : List ℝ) : l.map (fun t => t)=l := by
      induction l with
      | nil => rfl
      | cons t l ih => simpa only [List.map_cons] using congrArg (List.cons t) ih
    have hsum := List.sum_map_mul_left (terms a b is) (fun t => t) (b i)
    rw [hid] at hsum
    simp only [terms,List.sum_cons,List.map_cons,List.prod_cons,hsum,ih]
    ring

def remainder {I : Type*} (B E : I→ℝ) : List I→ℝ
  | [] => 0
  | i::is => B i*(is.map E).prod+E i*remainder B E is

theorem remainder_nonneg {I : Type*} (B E : I→ℝ) (hB : ∀ i,0≤B i) (hE : ∀ i,0≤E i)
    (is : List I) : 0≤remainder B E is := by
  induction is with
  | nil => exact le_refl _
  | cons i is ih =>
    exact add_nonneg (mul_nonneg (hB i) (List.prod_nonneg (fun x hx => by
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx;exact hE j))) (mul_nonneg (hE i) ih)

theorem prod_abs_le {I : Type*} (a E : I→ℝ) (hE : ∀ i,0≤E i)
    (ha : ∀ i,|a i|≤E i) (is : List I) : |(is.map a).prod|≤(is.map E).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons,List.prod_cons,abs_mul]
    exact mul_le_mul (ha i) ih (abs_nonneg _) (hE i)

theorem difference_bound {I : Type*} (a b B E : I→ℝ) {X : ℝ} (hX : 0≤X)
    (hB : ∀ i,0≤B i) (hE : ∀ i,0≤E i) (ha : ∀ i,|a i|≤E i)
    (hb : ∀ i,|b i|≤E i) (hpair : ∀ i,|a i-b i|≤X*B i) (is : List I) :
    |(is.map a).prod-(is.map b).prod|≤X*remainder B E is := by
  induction is with
  | nil => simp [remainder]
  | cons i is ih =>
    have he : (a i*(is.map a).prod-b i*(is.map b).prod)=
        (a i-b i)*(is.map a).prod+b i*((is.map a).prod-(is.map b).prod) := by ring
    simp only [List.map_cons,List.prod_cons]
    rw [he]
    have htri := abs_add_le ((a i-b i)*(is.map a).prod)
      (b i*((is.map a).prod-(is.map b).prod))
    simp only [abs_mul] at htri
    have hh := htri.trans
      (add_le_add (mul_le_mul (hpair i) (prod_abs_le a E hE ha is)
        (abs_nonneg _) (mul_nonneg hX (hB i)))
        (mul_le_mul (hb i) ih (abs_nonneg _) (hE i)))
    convert! hh using 1
    dsimp [remainder]
    ring

variable {n d r m : ℕ}

def factor (a : ℝ→ℝ) (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ)
    (mean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (x : (Fin r→State n)×State n) : Fin (m+1)→ℝ :=
  Fin.cases (VectorControlledRoot.value choices 0 F mean g x)
    (fun j => ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x)

theorem factor_product (a : ℝ→ℝ) (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ)
    (mean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n) (baseline : Fin m→ℝ)
    (x : (Fin r→State n)×State n) :
    (∏ i,factor a choices F mean g leaf baseline x i)=
      VectorControlledRoot.value choices 0 F mean g x*
        (∏ j,ControlledAssignedLeaf.leaf choices j.succ a mean (leaf j) (baseline j) x) := by
  simp only [factor,Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ]

/-- Literal actual canonical old-assigned word current-mean telescope.
Every unchanged old score and every original root/leaf factor remains;
there are no derivative or probabilistic assumptions in this identity. -/
theorem coefficientWord_difference (a : ℝ→ℝ) (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r→State n) (choices : List (Fin r×Fin (m+1))) (F : State d→ℝ)
    (newMean oldMean : State n) (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (baseline : Fin m→ℝ) (x : (Fin r→State n)×State n) :
    VectorControlledAssignedWord.coefficientWord a A D choices F newMean g leaf baseline x-
      VectorControlledAssignedWord.coefficientWord a A D choices F oldMean g leaf baseline x=
      (∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (x.1 j))*
        (terms (factor a choices F newMean g leaf baseline x)
          (factor a choices F oldMean g leaf baseline x) (List.ofFn (fun i : Fin (m+1) => i))).sum := by
  rw [terms_sum]
  simp only [List.map_ofFn,Fin.prod_ofFn,Function.comp_apply]
  rw [factor_product,factor_product]
  unfold VectorControlledAssignedWord.coefficientWord
  ring

end SHE.AssignedCurrentTelescope
