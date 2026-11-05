module

public import SHE.TriangularScoreWords
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.TriangularScoreWords
open Set MeasureTheory ProbabilityTheory GaussianIncrement
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X] {n r : ℕ}

theorem integrable_full_test (K : Fin r → Kernel X n) (F : State n → ℝ)
    (hF : Measurable F) (B : ℝ) (hb : ∀ z, |F z| ≤ B) (z : State n) :
    Integrable (fun x : Fin r → X => (∏ j, (K j).score (x j)) *
      F (z + ∑ j, (K j).shift (x j))) (Measure.pi (fun j => (K j).measure)) := by
  have hm : Measurable (fun x : Fin r → X => F (z + ∑ j, (K j).shift (x j))) :=
    hF.comp (measurable_const.add (Finset.measurable_sum Finset.univ
      (fun j _ => (K j).shift_measurable.comp (measurable_pi_apply j))))
  exact (Integrable.fintype_prod (fun j => (K j).score_integrable)).mul_bdd hm.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb (z + ∑ j, (K j).shift (x j))))

/-- Genuine finite-product Fubini for an arbitrary number of integrable
score kernels. The observations in the full test can be arbitrarily
dependent on the entire original tuple. -/
theorem actions_eq_integral (r : ℕ) (K : Fin r → Kernel X n) (F : State n → ℝ)
    (hF : Measurable F) (B : ℝ) (hb : ∀ z, |F z| ≤ B) (z : State n) :
    actions (List.ofFn K) F z =
      ∫ x : Fin r → X, (∏ j, (K j).score (x j)) * F (z + ∑ j, (K j).shift (x j))
        ∂Measure.pi (fun j => (K j).measure) := by
  induction r generalizing z with
  | zero =>
    have he : (Measure.pi (fun j : Fin 0 => (K j).measure)) Set.univ = 1 :=
      Measure.pi_empty_univ _
    simp [actions, Measure.real, he]
  | succ r ih =>
    let μ : Fin (r+1) → Measure X := fun j => (K j).measure
    let ν : Measure (Fin r → X) := Measure.pi (fun j => μ ((0 : Fin (r+1)).succAbove j))
    let insert := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => X) 0).symm
    have he :
        (fun p : X × (Fin r → X) => (∏ j, (K j).score (insert p j)) *
          F (z + ∑ j, (K j).shift (insert p j))) =
        fun p => (K 0).score p.1 * ((∏ j, (K j.succ).score (p.2 j)) *
          F (z + (K 0).shift p.1 + ∑ j, (K j.succ).shift (p.2 j))) := by
      funext p
      change (∏ j, (K j).score ((Fin.insertNth 0 p.1 p.2 : Fin (r+1) → X) j)) *
          F (z + ∑ j, (K j).shift ((Fin.insertNth 0 p.1 p.2 : Fin (r+1) → X) j)) = _
      rw [Fin.prod_univ_succAbove _ 0, Fin.sum_univ_succAbove _ 0]
      simp only [Fin.insertNth_apply_same, Fin.succAbove_zero]
      simp only [Fin.insertNth_zero', Fin.cons_succ]
      simp only [add_assoc]
      ring
    have hw := (K 0).score_integrable.mul_prod
      (Integrable.fintype_prod (fun j : Fin r => (K j.succ).score_integrable))
    have hm : Measurable (fun p : X × (Fin r → X) =>
        F (z + (K 0).shift p.1 + ∑ j, (K j.succ).shift (p.2 j))) :=
      hF.comp ((measurable_const.add ((K 0).shift_measurable.comp measurable_fst)).add
        (Finset.measurable_sum Finset.univ (fun j _ =>
          (K j.succ).shift_measurable.comp ((measurable_pi_apply j).comp measurable_snd))))
    have hbound : ∀ p : X × (Fin r → X),
        ‖F (z + (K 0).shift p.1 + ∑ j, (K j.succ).shift (p.2 j))‖ ≤ B := by
      intro p
      simpa only [Real.norm_eq_abs] using
        hb (z + (K 0).shift p.1 + ∑ j, (K j.succ).shift (p.2 j))
    have hint := hw.mul_bdd hm.aestronglyMeasurable (ae_of_all _ hbound)
    rw [List.ofFn_succ]
    change (∫ x, (K 0).score x * actions (List.ofFn (fun j : Fin r => K j.succ)) F
      (z + (K 0).shift x) ∂(K 0).measure) = _
    simp_rw [ih]
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
    change _ = ∫ p : X × (Fin r → X), (∏ j, (K j).score (insert p j)) *
      F (z + ∑ j, (K j).shift (insert p j)) ∂(μ 0).prod ν
    rw [he]
    have hint' : Integrable (fun p : X × (Fin r → X) => (K 0).score p.1 *
        ((∏ j, (K j.succ).score (p.2 j)) *
          F (z + (K 0).shift p.1 + ∑ j, (K j.succ).shift (p.2 j)))) ((μ 0).prod ν) := by
      convert! hint using 1
      funext p
      ring
    rw [MeasureTheory.integral_prod _ hint']
    apply integral_congr_ae
    apply ae_of_all
    intro x
    exact (integral_const_mul _ _).symm

/-- An all-order triangular word is one genuine product score integral
of its original full root/leaf test. Boundedness is needed only for that
full test, rather than independently bounded score integrands. -/
theorem word_eq_integral (word : Word X n) (hword : Triangular word)
    (F : State n → ℝ) (hF : Measurable (fullTest word F))
    (B : ℝ) (hb : ∀ z, |fullTest word F z| ≤ B) (z : State n) :
    apply word F z =
      ∫ x : Fin word.length → X,
        (∏ j, (word.get j).1.score (x j)) *
          fullTest word F (z + ∑ j, (word.get j).1.shift (x j))
        ∂Measure.pi (fun j => (word.get j).1.measure) := by
  have he : List.ofFn (fun j : Fin word.length => (word.get j).1) = word.map Prod.fst := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map Prod.fst) (List.ofFn_get word)
  rw [apply_eq_actions_fullTest word hword F]
  rw [← he]
  exact actions_eq_integral _ _ _ hF B hb z

end SHE.TriangularScoreWords
