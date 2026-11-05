module

public import SHE.FiniteDifferences
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.VectorFiniteDifferences
open Set
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def mixed : List E → (E → F) → E → F
  | [], f => f
  | z::zs, f => fun x => mixed zs f (x+z) - mixed zs f x

def clips (ν : ℝ) (zs : List E) : ℝ :=
  (zs.map fun z => min 1 (ν*‖z‖)).prod

theorem clips_nonneg {ν : ℝ} (hν : 0 ≤ ν) (zs : List E) : 0 ≤ clips ν zs := by
  induction zs with
  | nil => simp [clips]
  | cons z zs ih =>
    simpa [clips] using mul_nonneg
      (le_min (by norm_num) (mul_nonneg hν (norm_nonneg z))) ih

theorem mixed_hasFDerivAt (f : E → F) (df : E → E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (df x) x) (zs : List E) (x : E) :
    HasFDerivAt (mixed zs f) (mixed zs df x) x := by
  induction zs generalizing x with
  | nil => exact hf x
  | cons z zs ih =>
    exact ((hasFDerivAt_comp_add_right z).mpr (ih (x+z))).sub (ih x)

/-- The Bernstein clip for one vector increment follows from the actual
Fréchet derivative, including vector-valued intermediate derivatives. -/
theorem difference_clipped_bound {f : E → F} {df : E → E →L[ℝ] F} {A ν : ℝ}
    (hA : 0 ≤ A) (hν : 0 ≤ ν) (hf : ∀ x, HasFDerivAt f (df x) x)
    (hb : ∀ x, ‖f x‖ ≤ A) (hd : ∀ x, ‖df x‖ ≤ A*ν) (z x : E) :
    ‖f (x+z)-f x‖ ≤ 2*A*min 1 (ν*‖z‖) := by
  have hlarge : ‖f (x+z)-f x‖ ≤ 2*A :=
    (norm_sub_le _ _).trans (by linarith [hb (x+z), hb x])
  have hsmall : ‖f (x+z)-f x‖ ≤ A*ν*‖z‖ := by
    simpa only [add_sub_cancel_left] using
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (s := univ) (f := f) (f' := df) (C := A*ν)
        (fun y _ => (hf y).hasFDerivWithinAt) (fun y _ => hd y)
        convex_univ (mem_univ x) (mem_univ (x+z))
  by_cases hz : ν*‖z‖ ≤ 1
  · rw [min_eq_right hz]
    nlinarith [mul_nonneg hA (mul_nonneg hν (norm_nonneg z))]
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hz))]
    simpa only [mul_one] using hlarge

/-- A finite Fréchet jet controls all assigned root differences. No
scalar projection restriction or infinite derivative tower is assumed. -/
theorem mixed_clipped_bound_finite (N : ℕ) :
    ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → F) (zs : List E), zs.length ≤ N →
      ∀ {A ν : ℝ}, 0 ≤ A → 0 ≤ ν → ContDiff ℝ N f →
      (∀ j, j ≤ N → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A*ν^j) →
      ∀ x, ‖mixed zs f x‖ ≤ 2^zs.length*A*clips ν zs := by
  induction N with
  | zero =>
    intro E F _ _ _ _ f zs hz A ν hA hν hf hb x
    have hz' : zs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hz)
    subst zs
    simpa [mixed, clips, norm_iteratedFDeriv_zero] using hb 0 le_rfl x
  | succ N ih =>
    intro E F _ _ _ _ f zs hz A ν hA hν hf hb x
    cases zs with
    | nil => simpa [mixed, clips, norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le _) x
    | cons z zs =>
      have hlen : zs.length ≤ N := by simp only [List.length_cons] at hz; omega
      have hcf : ContDiff ℝ N f := hf.of_le (by exact_mod_cast Nat.le_succ N)
      have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
      have hdf : ContDiff ℝ N (fderiv ℝ f) := hf.fderiv_right (by simp)
      have hbase := ih E F f zs hlen hA hν hcf
        (fun j hj y => hb j (hj.trans (Nat.le_succ N)) y)
      have hderiv := ih E (E →L[ℝ] F) (fderiv ℝ f) zs hlen
        (mul_nonneg hA hν) hν hdf (fun j hj y => by
          rw [norm_iteratedFDeriv_fderiv]
          calc
            _ ≤ A*ν^(j+1) := hb (j+1) (Nat.succ_le_succ hj) y
            _ = (A*ν)*ν^j := by rw [pow_succ]; ring)
      have hpos : 0 ≤ 2^zs.length*A*clips ν zs := by
        exact mul_nonneg (mul_nonneg (by positivity) hA) (clips_nonneg hν zs)
      have hd (y : E) : ‖mixed zs (fderiv ℝ f) y‖ ≤ (2^zs.length*A*clips ν zs)*ν := by
        convert hderiv y using 1 <;> ring
      have h := difference_clipped_bound hpos hν
        (mixed_hasFDerivAt f (fderiv ℝ f) (fun y => (hdiff y).hasFDerivAt) zs)
        hbase hd z x
      calc
        _ ≤ 2*(2^zs.length*A*clips ν zs)*min 1 (ν*‖z‖) := h
        _ = _ := by simp only [List.length_cons,pow_succ,clips,List.map_cons,List.prod_cons]; ring

end SHE.VectorFiniteDifferences
