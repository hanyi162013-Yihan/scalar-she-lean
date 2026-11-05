module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.PowerTaylorBound
open Set

/-- First-order Taylor bound on a bounded segment, with an explicit
homogeneous second-order remainder. It applies to every integer power. -/
theorem remainder (k : ℕ) (hk : 2 ≤ k) (x y D : ℝ)
    (hD : 0 ≤ D) (hx : |x| ≤ D) (hy : |y| ≤ D) :
    |y^k-x^k-(k : ℝ)*x^(k-1)*(y-x)| ≤
      (k : ℝ)*(k-1 : ℕ)*D^(k-2)*(y-x)^2 := by
  let d := y-x
  let g (t : ℝ) := (x+t*d)^k-x^k-t*((k : ℝ)*x^(k-1)*d)
  let g' (t : ℝ) := (k : ℝ)*((x+t*d)^(k-1)-x^(k-1))*d
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ ↦ x+t*d) d t := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id t).mul_const d).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    convert (((hd t).pow k).sub_const (x^k)).sub
      ((hasDerivAt_id t).mul_const ((k : ℝ)*x^(k-1)*d)) using 1
    · rfl
    · dsimp only [g']; ring
  have hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |x+t*d| ≤ D := by
    have he : x+t*d = (1-t)*x+t*y := by dsimp only [d]; ring
    rw [he]
    calc
      _ ≤ |(1-t)*x|+|t*y| := abs_add_le _ _
      _ = (1-t)*|x|+t*|y| := by rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
      _ ≤ (1-t)*D+t*D := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hy ht.1)
      _ = D := by ring
  let B := (k : ℝ)*(k-1 : ℕ)*D^(k-2)*d^2
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖g' t‖ ≤ B := by
    have hm : max |x+t*d| |x| ≤ D := max_le (hz t ht) hx
    have hdt : |x+t*d-x| ≤ |d| := by
      have he : x+t*d-x = t*d := by ring
      rw [he, abs_mul, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg d) ht.2
    have hp : |(x+t*d)^(k-1)-x^(k-1)| ≤ |d| *(k-1 : ℕ)*D^(k-2) := by
      have hh := abs_pow_sub_pow_le (a := x+t*d) (b := x) (n := k-1)
      have hn : k-1-1 = k-2 := by omega
      rw [hn] at hh
      exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hdt (Nat.cast_nonneg _))
        (pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hm _) (by positivity) (by positivity))
    calc
      ‖g' t‖ = (k : ℝ)*|(x+t*d)^(k-1)-x^(k-1)| *|d| := by
        simp only [g', Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      _ ≤ (k : ℝ)*(|d| *(k-1 : ℕ)*D^(k-2))*|d| := by gcongr
      _ = (k : ℝ)*(k-1 : ℕ)*D^(k-2)*|d|^2 := by ring
      _ = B := by rw [sq_abs]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ (hg t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [g, B, d, zero_mul, add_zero, sub_self, sub_zero, one_mul,
    add_sub_cancel, norm_one, mul_one, Real.norm_eq_abs] using hh

/-- A homogeneous Young bound proved by splitting at y=εx. -/
theorem young (p : ℕ) (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^(p-1)*y ≤ ε*x^p+ε⁻¹^(p-1)*y^p := by
  have hn : p-1+1 = p := by omega
  by_cases h : y ≤ ε*x
  · calc
      _ ≤ x^(p-1)*(ε*x) := mul_le_mul_of_nonneg_left h (pow_nonneg hx _)
      _ = ε*x^p := by
        have he : x^(p-1)*x = x^p := by simpa only [hn] using (pow_succ x (p-1)).symm
        calc
          _ = ε*(x^(p-1)*x) := by ring
          _ = _ := congrArg (fun z : ℝ ↦ ε*z) he
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hxy : x ≤ ε⁻¹*y := by
      have hh : x ≤ y/ε := (le_div_iff₀ hε).mpr (by linarith [lt_of_not_ge h])
      simpa only [div_eq_mul_inv, mul_comm] using hh
    calc
      _ ≤ (ε⁻¹*y)^(p-1)*y := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy _) hy
      _ = ε⁻¹^(p-1)*y^p := by
        have he : y^(p-1)*y = y^p := by simpa only [hn] using (pow_succ y (p-1)).symm
        rw [mul_pow, mul_assoc, he]
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

end SHEStochastic.PowerTaylorBound
