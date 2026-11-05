module

public import SHE.GaussianVectorFractions
public import SHE.FiniteCenteredProduct

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianFractionBaselines
open Set MeasureTheory GaussianIncrement GaussianVectorFractions FiniteCenteredProduct
open scoped BigOperators
variable {E : Type*} [Zero E] {n : ℕ}

/-- Every nonempty old-fraction block annihilates the deterministic leaf
baseline exactly, before any absolute values or moment bounds are taken. -/
theorem fractionDifferences_sub_const (is : List (Fin n)) (his : is ≠ [])
    (F : (Fin n → E) → ℝ) (c : ℝ) :
    fractionDifferences is (fun x => F x - c) = fractionDifferences is F := by
  induction is with
  | nil => exact (his rfl).elim
  | cons i is ih =>
    cases is with
    | nil =>
      funext x
      simp only [fractionDifferences, List.foldr_cons, List.foldr_nil, fractionDifference]
      ring
    | cons j js =>
      change fractionDifference i (fractionDifferences (j :: js) (fun x => F x - c)) = _
      rw [ih (List.cons_ne_nil j js)]
      rfl

theorem nonempty_baseline_hasDerivAt (is : List (Fin n)) (his : is ≠ [])
    (F : (Fin n → E) → ℝ) (b : ℝ → ℝ) (θ : ℝ) (x : Fin n → E) :
    HasDerivAt (fun η => fractionDifferences is (fun y => F y - b η) x) 0 θ := by
  have he : (fun η => fractionDifferences is (fun y => F y - b η) x) =
      fun _ => fractionDifferences is F x := by
    funext η
    rw [fractionDifferences_sub_const is his]
  rw [he]
  exact hasDerivAt_const θ _

def leaf (is : List (Fin n)) (F : (Fin n → E) → ℝ) (b : ℝ) (x : Fin n → E) : ℝ :=
  fractionDifferences is (fun y => F y - b) x

theorem leaf_hasDerivAt (is : List (Fin n)) (F : (Fin n → E) → ℝ)
    (b : ℝ → ℝ) (db θ : ℝ) (hb : HasDerivAt b db θ) (x : Fin n → E) :
    HasDerivAt (fun η => leaf is F (b η) x) (if is = [] then -db else 0) θ := by
  by_cases hi : is = []
  · subst is
    convert! (hasDerivAt_const θ (F x)).sub hb using 1 <;>
      simp only [leaf, fractionDifferences, List.foldr_nil, ite_true, zero_sub, Pi.sub_apply]
  · simpa only [leaf, hi, ite_false] using nonempty_baseline_hasDerivAt is hi F b θ x

variable {ι : Type*} [DecidableEq ι]

/-- In an arbitrary assigned finite word, only unassigned leaves retain
explicit baseline derivatives. A leaf with any nonempty centered block
contributes exactly zero; all other old blocks and the root stay fixed. -/
theorem product_baseline_hasDerivAt (s : Finset ι) (blocks : ι → List (Fin n))
    (F : ι → (Fin n → E) → ℝ) (R : (Fin n → E) → ℝ)
    (b : ι → ℝ → ℝ) (db : ι → ℝ) (θ : ℝ)
    (hb : ∀ i ∈ s, HasDerivAt (b i) (db i) θ) (x : Fin n → E) :
    HasDerivAt (fun η => R x * ∏ i ∈ s, leaf (blocks i) (F i) (b i η) x)
      (-(∑ i ∈ s.filter (fun i => blocks i = []), db i *
        (R x * ∏ j ∈ s.erase i, leaf (blocks j) (F j) (b j θ) x))) θ := by
  classical
  have hh := (HasDerivAt.fun_finsetProd (u := s)
    (fun i hi => leaf_hasDerivAt (blocks i) (F i) (b i) (db i) θ (hb i hi) x)).const_mul (R x)
  convert hh using 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : blocks i = [] <;> simp only [hb, ite_true, ite_false, smul_eq_mul]
  · ring
  · ring

end SHE.GaussianFractionBaselines
