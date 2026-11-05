module

public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! Exact centering for actual finite-dimensional Gaussian fractions, with
all observation coordinates retained in the bounded measurable test. -/
namespace SHE.GaussianVectorFractions
open Set MeasureTheory ProbabilityTheory GaussianIncrement MeasurableGaussianScores
open scoped InnerProductSpace
variable {E : Type*} [MeasurableSpace E] [Zero E]

def fractionDifference {n : ℕ} (i : Fin n) (F : (Fin n → E) → ℝ)
    (x : Fin n → E) : ℝ := F x - F (Function.update x i 0)

def fractionDifferences {n : ℕ} (is : List (Fin n)) (F : (Fin n → E) → ℝ) :
    (Fin n → E) → ℝ := is.foldr fractionDifference F

theorem measurable_fractionDifference {n : ℕ} (i : Fin n)
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    Measurable (fractionDifference i F) := by
  unfold fractionDifference
  exact hF.sub (hF.comp (by fun_prop))

omit [MeasurableSpace E] in
theorem fractionDifference_bound {n : ℕ} (i : Fin n)
    (F : (Fin n → E) → ℝ) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (x : Fin n → E) :
    |fractionDifference i F x| ≤ 2 * M := by
  exact (abs_sub _ _).trans (by linarith [hB x, hB (Function.update x i 0)])

/-- A centered coordinate score annihilates every test in which that
coordinate has been suppressed. This is the actual finite-product integral,
proved by a measure-preserving coordinate split and Fubini. -/
theorem integral_product_score_suppressed {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ j, SigmaFinite (μ j)]
    (S : Fin (n + 1) → E → ℝ) (i : Fin (n + 1))
    (hSi : ∫ z, S i z ∂μ i = 0) (F : (Fin (n + 1) → E) → ℝ) :
    (∫ x, (∏ j, S j (x j)) * F (Function.update x i 0) ∂Measure.pi μ) = 0 := by
  rw [← ((measurePreserving_piFinSuccAbove μ i).symm).integral_comp']
  have heq : (fun p : E × (Fin n → E) =>
      (∏ j, S j (((MeasurableEquiv.piFinSuccAbove (fun _ => E) i).symm p) j)) *
        F (Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ => E) i).symm p) i 0)) =
      fun p => S i p.1 * ((∏ j : Fin n, S (i.succAbove j) (p.2 j)) *
        F (Fin.insertNth i 0 p.2)) := by
    funext ⟨z, x⟩
    change (∏ j, S j ((Fin.insertNth i z x : Fin (n + 1) → E) j)) *
      F (Function.update (Fin.insertNth i z x) i 0) = _
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      Fin.update_insertNth]
    ring
  rw [heq]
  calc
    _ = (∫ z, S i z ∂μ i) *
        ∫ x, (∏ j : Fin n, S (i.succAbove j) (x j)) * F (Fin.insertNth i 0 x)
          ∂Measure.pi (fun j => μ (i.succAbove j)) := integral_prod_mul _ _
    _ = 0 := by rw [hSi, zero_mul]

omit [Zero E] in
theorem integrable_product_score_bounded {n : ℕ}
    (μ : Fin n → Measure E) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → E → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (F : (Fin n → E) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    Integrable (fun x => (∏ j, S j (x j)) * F x) (Measure.pi μ) := by
  exact (Integrable.fintype_prod hS).mul_bdd hF.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))

/-- Exact preservation of a finite Gaussian-score word by one old-fraction
centering, with integrability proved from the actual score moments. -/
theorem integral_product_score_fractionDifference {n : ℕ}
    (μ : Fin n → Measure E) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → E → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (i : Fin n) (hSi : ∫ z, S i z ∂μ i = 0)
    (F : (Fin n → E) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ x, (∏ j, S j (x j)) * fractionDifference i F x ∂Measure.pi μ) =
      ∫ x, (∏ j, S j (x j)) * F x ∂Measure.pi μ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have h₁ := integrable_product_score_bounded μ S hS F hF M hB
    have h₂ := integrable_product_score_bounded μ S hS
      (fun x => F (Function.update x i 0)) (hF.comp (by fun_prop)) M (fun x => hB _)
    simp only [fractionDifference, mul_sub]
    rw [integral_sub h₁ h₂, integral_product_score_suppressed μ S i hSi, sub_zero]

theorem measurable_fractionDifferences {n : ℕ} (is : List (Fin n))
    (F : (Fin n → E) → ℝ) (hF : Measurable F) :
    Measurable (fractionDifferences is F) := by
  induction is with
  | nil => exact hF
  | cons i is ih => exact measurable_fractionDifference i _ ih

omit [MeasurableSpace E] in
theorem fractionDifferences_bound {n : ℕ} (is : List (Fin n))
    (F : (Fin n → E) → ℝ) (M : ℝ) (hB : ∀ x, |F x| ≤ M) (x : Fin n → E) :
    |fractionDifferences is F x| ≤ 2 ^ is.length * M := by
  induction is generalizing x with
  | nil => simpa [fractionDifferences] using hB x
  | cons i is ih =>
    have h := fractionDifference_bound i (fractionDifferences is F)
      (2 ^ is.length * M) (fun x => ih x) x
    simpa [fractionDifferences, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- Every finite family of independent centered scores admits the full
iterated old-fraction centering. This is an identity for the actual product
measure and a bounded measurable test, not a formal assumed cancellation. -/
theorem integral_product_score_fractionDifferences {n : ℕ}
    (μ : Fin n → Measure E) [∀ j, SigmaFinite (μ j)]
    (S : Fin n → E → ℝ) (hS : ∀ j, Integrable (S j) (μ j))
    (hS0 : ∀ j, ∫ z, S j z ∂μ j = 0) (is : List (Fin n))
    (F : (Fin n → E) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ x, (∏ j, S j (x j)) * fractionDifferences is F x ∂Measure.pi μ) =
      ∫ x, (∏ j, S j (x j)) * F x ∂Measure.pi μ := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (∫ x, (∏ j, S j (x j)) * fractionDifference i (fractionDifferences is F) x
      ∂Measure.pi μ) = _
    rw [integral_product_score_fractionDifference μ S hS i (hS0 i)
      (fractionDifferences is F) (measurable_fractionDifferences is F hF)
      (2 ^ is.length * M) (fractionDifferences_bound is F M hB), ih]


section Assignment
omit [MeasurableSpace E]
theorem fractionDifference_product {n m : ℕ} (i : Fin n)
    (F : Fin m → (Fin n → E) → ℝ) (x : Fin n → E) :
    fractionDifference i (fun y => ∏ j, F j y) x =
      ∑ j : Fin m, fractionDifference i (F j) x *
        (∏ k ∈ Finset.univ with k < j, F k (Function.update x i 0)) *
        ∏ k ∈ Finset.univ with j < k, F k x := by
  have h := Finset.prod_sub_ordered (Finset.univ : Finset (Fin m))
    (fun j => F j x) (fun j => F j x - F j (Function.update x i 0))
  simp only [sub_sub_cancel] at h
  dsimp [fractionDifference]
  linarith

theorem fractionDifference_mul {n : ℕ} (i : Fin n)
    (F G : (Fin n → E) → ℝ) (x : Fin n → E) :
    fractionDifference i (fun y => F y * G y) x =
      fractionDifference i F x * G x +
        F (Function.update x i 0) * fractionDifference i G x := by
  dsimp [fractionDifference]
  ring

/-- If a newest rough leaf is untouched by all old fractions, it survives
every old centering exactly as a factor. -/
theorem fractionDifferences_mul_const {n : ℕ} (is : List (Fin n))
    (F : (Fin n → E) → ℝ) (c : ℝ) :
    fractionDifferences is (fun x => F x * c) =
      fun x => fractionDifferences is F x * c := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change fractionDifference i (fractionDifferences is (fun x => F x * c)) = _
    rw [ih]
    funext x
    dsimp [fractionDifferences, fractionDifference]
    ring

/-- One term of the ordered assignment of one fraction to one factor. The
three exclusive cases are an earlier suppressed factor, the chosen difference,
and a later unchanged factor. -/
def assignFractionFactor {n m : ℕ} (i : Fin n)
    (F : Fin m → (Fin n → E) → ℝ) (j k : Fin m) (x : Fin n → E) : ℝ :=
  (if k < j then F k (Function.update x i 0) else 1) *
    (if k = j then fractionDifference i (F k) x else 1) *
    (if j < k then F k x else 1)

theorem product_assignFractionFactor {n m : ℕ} (i : Fin n)
    (F : Fin m → (Fin n → E) → ℝ) (j : Fin m) (x : Fin n → E) :
    (∏ k, assignFractionFactor i F j k x) =
      fractionDifference i (F j) x *
        (∏ k ∈ Finset.univ with k < j, F k (Function.update x i 0)) *
        ∏ k ∈ Finset.univ with j < k, F k x := by
  simp only [assignFractionFactor, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  rw [← Finset.prod_filter, ← Finset.prod_filter]
  ring

/-- The explicit finite list of factor assignments. At each old fraction
there is exactly one choice of root/rough factor. Its list length is m^n
(including duplicate terms when a difference happens to vanish). -/
def fractionAssignmentFamilies {n m : ℕ} (is : List (Fin n))
    (F : Fin m → (Fin n → E) → ℝ) : List (Fin m → (Fin n → E) → ℝ) :=
  match is with
  | [] => [F]
  | i :: is => (fractionAssignmentFamilies is F).flatMap
      (fun G => List.ofFn (fun j => assignFractionFactor i G j))

def sumProductFamilies {n m : ℕ} (l : List (Fin m → (Fin n → E) → ℝ))
    (x : Fin n → E) : ℝ := (l.map (fun F => ∏ j, F j x)).sum

theorem fractionDifference_sumProductFamilies {n m : ℕ} (i : Fin n)
    (l : List (Fin m → (Fin n → E) → ℝ)) (x : Fin n → E) :
    fractionDifference i (sumProductFamilies l) x =
      (l.map (fun F => fractionDifference i (fun y => ∏ j, F j y) x)).sum := by
  induction l with
  | nil => simp [fractionDifference, sumProductFamilies]
  | cons F l ih =>
    simp only [sumProductFamilies, List.map_cons, List.sum_cons, fractionDifference] at ih ⊢
    linarith

omit [Zero E] in
theorem sumProductFamilies_flatMap {n m : ℕ}
    (l : List (Fin m → (Fin n → E) → ℝ))
    (f : (Fin m → (Fin n → E) → ℝ) → List (Fin m → (Fin n → E) → ℝ))
    (x : Fin n → E) :
    sumProductFamilies (l.flatMap f) x =
      (l.map (fun F => sumProductFamilies (f F) x)).sum := by
  induction l with
  | nil => simp [sumProductFamilies]
  | cons F l ih =>
    simpa only [sumProductFamilies, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] using congrArg
        (fun a => sumProductFamilies (f F) x + a) ih

/-- An explicit all-order product assignment expansion, obtained by iterating
the exact one-fraction Leibniz rule. No smoothness or stochastic estimate is
used; the same original observation tuple remains in every test factor. -/
theorem fractionDifferences_assignment_expansion {n m : ℕ}
    (is : List (Fin n)) (F : Fin m → (Fin n → E) → ℝ) (x : Fin n → E) :
    fractionDifferences is (fun y => ∏ j, F j y) x =
      sumProductFamilies (fractionAssignmentFamilies is F) x := by
  induction is generalizing x with
  | nil => simp [fractionDifferences, fractionAssignmentFamilies, sumProductFamilies]
  | cons i is ih =>
    have heq : fractionDifferences is (fun y => ∏ j, F j y) =
        sumProductFamilies (fractionAssignmentFamilies is F) := funext ih
    change fractionDifference i (fractionDifferences is (fun y => ∏ j, F j y)) x = _
    rw [heq, fractionDifference_sumProductFamilies]
    rw [fractionAssignmentFamilies, sumProductFamilies_flatMap]
    congr 1
    apply List.map_congr_left
    intro G hG
    rw [fractionDifference_product]
    simp only [sumProductFamilies, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    apply Finset.sum_congr rfl
    intro j hj
    exact (product_assignFractionFactor i G j x).symm


end Assignment

theorem gaussian_secondScore_integrable {m : ℕ}
    (A : MeasurableGeneralizedInverse.Mat m) (d : State m) :
    Integrable (secondScore A d) (multivariateGaussian 0 A) := by
  have h := (IsGaussian.memLp_dual (multivariateGaussian (0 : State m) A)
    (innerSL ℝ (coefficient A d)) 2 (by norm_num)).integrable_sq.sub (integrable_const (scoreVariance A d))
  convert! h using 1

/-- Each old interval may reserve a full Gaussian observation vector with
its actual singular covariance. Centering suppresses only that independent
fraction, while the bounded test keeps the complete original point list. -/
theorem gaussian_vector_scores_center_all {n m : ℕ}
    (A : Fin n → MeasurableGeneralizedInverse.Mat m) (hA : ∀ j, (A j).PosSemidef)
    (d : Fin n → State m)
    (hd : ∀ j, d j ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)).range)
    (is : List (Fin n)) (F : (Fin n → State m) → ℝ) (hF : Measurable F)
    (M : ℝ) (hB : ∀ x, |F x| ≤ M) :
    (∫ x, (∏ j, secondScore (A j) (d j) (x j)) * fractionDifferences is F x
      ∂Measure.pi (fun j => multivariateGaussian 0 (A j))) =
      ∫ x, (∏ j, secondScore (A j) (d j) (x j)) * F x
        ∂Measure.pi (fun j => multivariateGaussian 0 (A j)) := by
  exact integral_product_score_fractionDifferences _ _
    (fun j => gaussian_secondScore_integrable (A j) (d j))
    (fun j => secondScore_mean_zero (hA j) (hd j)) is F hF M hB

/-- The genuine finite-dimensional covariance-fraction word equals its
explicit all-order root/rough assignment expansion. The covariance ranks
and the physical directions may vary from fraction to fraction. -/
theorem gaussian_vector_word_assignment_identity {n m k : ℕ}
    (A : Fin n → MeasurableGeneralizedInverse.Mat m) (hA : ∀ j, (A j).PosSemidef)
    (d : Fin n → State m)
    (hd : ∀ j, d j ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)).range)
    (is : List (Fin n)) (F : Fin k → (Fin n → State m) → ℝ)
    (hF : ∀ j, Measurable (F j)) (M : ℝ) (hB : ∀ x, |∏ j, F j x| ≤ M) :
    (∫ x, (∏ j, secondScore (A j) (d j) (x j)) * (∏ j, F j x)
      ∂Measure.pi (fun j => multivariateGaussian 0 (A j))) =
      ∫ x, (∏ j, secondScore (A j) (d j) (x j)) *
        sumProductFamilies (fractionAssignmentFamilies is F) x
          ∂Measure.pi (fun j => multivariateGaussian 0 (A j)) := by
  rw [← gaussian_vector_scores_center_all A hA d hd is (fun y => ∏ j, F j y)
    (by fun_prop) M hB]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [fractionDifferences_assignment_expansion]))

end SHE.GaussianVectorFractions
