module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.SeparatedSums
open Finset
open scoped InnerProductSpace

theorem gram_lower_bound {I : Type*} [Fintype I] (A : I → I → ℝ) (d : I → ℝ)
    (_hd : ∀ i, 0 ≤ d i) {ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i, A i i = d i^2)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ ε*d i*d j) :
    (1-ε*(Fintype.card I:ℝ))*(∑ i, d i^2) ≤ ∑ i, ∑ j, A i j := by
  classical
  have hpoint (i j : I) : (if i=j then d i^2 else 0)-ε*d i*d j ≤ A i j := by
    by_cases hij : i=j
    · subst j
      rw [ite_eq_left rfl,hdiag]
      nlinarith [mul_nonneg hε (sq_nonneg (d i))]
    · rw [ite_eq_right hij,zero_sub]
      have hh := (abs_le.mp (hoff i j hij)).1
      linarith
  have hsum := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun j _ => hpoint i j))
  have he : (∑ i, ∑ j, ((if i=j then d i^2 else 0)-ε*d i*d j)) =
      (∑ i,d i^2)-ε*(∑ i,d i)^2 := by
    simp only [sum_sub_distrib,← mul_sum,← sum_mul]
    simp only [sum_ite_eq,mem_univ,ite_true]
    ring
  rw [he] at hsum
  have hCS := sq_sum_le_card_mul_sum_sq (s := univ) (f := d)
  simp only [card_univ] at hCS
  have hh := mul_le_mul_of_nonneg_left hCS hε
  nlinarith

theorem norm_sum_sq_lower {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u : I → E)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hoff : ∀ i j, i ≠ j → ‖inner ℂ (u i) (u j)‖ ≤ ε*‖u i‖*‖u j‖) :
    (1-ε*(Fintype.card I:ℝ))*(∑ i,‖u i‖^2) ≤ ‖∑ i,u i‖^2 := by
  have hdiag (i : I) : RCLike.re (inner ℂ (u i) (u i)) = ‖u i‖^2 := inner_self_eq_norm_sq _
  have hreal (i j : I) (hij : i ≠ j) :
      |RCLike.re (inner ℂ (u i) (u j))| ≤ ε*‖u i‖*‖u j‖ :=
    (RCLike.abs_re_le_norm _).trans (hoff i j hij)
  have hh := gram_lower_bound (fun i j => RCLike.re (inner ℂ (u i) (u j)))
    (fun i => ‖u i‖) (fun i => norm_nonneg _) hε hdiag hreal
  have he : ‖∑ i,u i‖^2 = ∑ i, ∑ j, RCLike.re (inner ℂ (u i) (u j)) := by
    rw [← inner_self_eq_norm_sq (𝕜:=ℂ) (∑ i,u i)]
    simp only [sum_inner (𝕜:=ℂ),inner_sum (𝕜:=ℂ),map_sum]
  rw [he]
  exact hh

theorem half_energy_bound {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u : I → E)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε*(Fintype.card I:ℝ) ≤ 1/2)
    (hoff : ∀ i j, i ≠ j → ‖inner ℂ (u i) (u j)‖ ≤ ε*‖u i‖*‖u j‖) :
    (∑ i,‖u i‖^2) ≤ 2*‖∑ i,u i‖^2 := by
  have hh := norm_sum_sq_lower u hε hoff
  have he := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-ε*(Fintype.card I:ℝ) by linarith)
    (sum_nonneg (s := univ) (fun i _ => sq_nonneg ‖u i‖))
  linarith

/-- Positive cluster envelopes combine with the checked Hilbert energy
bound. Both the pointwise and energy inequalities concern the actual
finite sums. -/
theorem sum_envelope_of_energy_bound {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : I → E) (f : I → ℂ) (w : I → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, ‖f i‖^2 ≤ C*‖u i‖^2*w i)
    (henergy : (∑ i,‖u i‖^2) ≤ B) :
    ‖∑ i,f i‖^2 ≤ (Fintype.card I:ℝ)*C*B*(∑ i,w i) := by
  have hN : 0 ≤ (Fintype.card I:ℝ) := by positivity
  have hE (i : I) : ‖u i‖^2 ≤ ∑ j,‖u j‖^2 :=
    single_le_sum (fun j _ => sq_nonneg ‖u j‖) (mem_univ i)
  have hsum : (∑ i,‖f i‖^2) ≤ C*(∑ i,‖u i‖^2)*(∑ i,w i) := by
    calc
      _ ≤ ∑ i,C*‖u i‖^2*w i := sum_le_sum (fun i _ => hf i)
      _ ≤ ∑ i,C*(∑ j,‖u j‖^2)*w i := sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE i) hC) (hw i))
      _ = _ := (mul_sum _ _ _).symm
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left henergy hC)
    (sum_nonneg (s := univ) (fun i _ => hw i))
  calc
    _ ≤ (∑ i,‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Fintype.card I:ℝ)*(∑ i,‖f i‖^2) := by
      simpa only [card_univ] using sq_sum_le_card_mul_sum_sq (s:=univ) (f:=fun i => ‖f i‖)
    _ ≤ (Fintype.card I:ℝ)*(C*(∑ i,‖u i‖^2)*(∑ i,w i)) := mul_le_mul_of_nonneg_left hsum hN
    _ ≤ (Fintype.card I:ℝ)*(C*B*(∑ i,w i)) := mul_le_mul_of_nonneg_left he hN
    _ = _ := by ring

theorem separated_sum_envelope {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : I → E) (f : I → ℂ) (w : I → ℝ) {C ε : ℝ} (hC : 0 ≤ C)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, ‖f i‖^2 ≤ C*‖u i‖^2*w i)
    (hε : 0 ≤ ε) (hsmall : ε*(Fintype.card I:ℝ) ≤ 1/2)
    (hoff : ∀ i j, i ≠ j → ‖inner ℂ (u i) (u j)‖ ≤ ε*‖u i‖*‖u j‖) :
    ‖∑ i,f i‖^2 ≤ (2*(Fintype.card I:ℝ)*C)*‖∑ i,u i‖^2*(∑ i,w i) := by
  have hh := sum_envelope_of_energy_bound u f w hC hw hf (half_energy_bound u hε hsmall hoff)
  convert hh using 1
  ring

end SHE.SeparatedSums
