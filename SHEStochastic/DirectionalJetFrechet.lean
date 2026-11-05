module

public import SHEStochastic.DirectionalJets
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.DirectionalJets
open scoped ContDiff

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The mixed directional jets used in the matrix recurrences are the
actual iterated Fréchet derivatives. The reversal accounts for the
first-direction-first convention of `jet`. -/
theorem eq_iterated {f : E → A} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (n : ℕ) (v : Fin n → E) :
    jet (List.ofFn v).reverse f x = iteratedFDeriv ℝ n f x v := by
  induction n generalizing f with
  | zero => simp only [List.ofFn_zero, List.reverse_nil, jet, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat]
    change jet (List.ofFn (Fin.init v)).reverse (directional (v (Fin.last n)) f) x = _
    rw [ih (directional_smooth hf (v (Fin.last n)))]
    let L : (E →L[ℝ] A) →L[ℝ] A := ContinuousLinearMap.apply ℝ A (v (Fin.last n))
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
    have hh := L.iteratedFDeriv_comp_left hd (by simp : (n : WithTop ℕ∞) ≤ ∞)
    have he : directional (v (Fin.last n)) f = L ∘ fderiv ℝ f := rfl
    rw [he, hh, iteratedFDeriv_succ_apply_right]
    rfl

end SHEStochastic.DirectionalJets
