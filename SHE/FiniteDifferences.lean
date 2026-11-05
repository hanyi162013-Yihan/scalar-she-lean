module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.FiniteDifferences

def difference (z : ℝ) (f : ℝ → ℝ) (x : ℝ) := f (x+z)-f x

def mixed : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | z::zs, f => difference z (mixed zs f)

def clips (ν : ℝ) (zs : List ℝ) := (zs.map fun z => min 1 (ν*|z|)).prod

theorem clips_nonneg {ν : ℝ} (hν : 0 ≤ ν) (zs : List ℝ) : 0 ≤ clips ν zs := by
  induction zs with
  | nil => simp [clips]
  | cons z zs ih => simpa [clips] using mul_nonneg (le_min (by norm_num) (mul_nonneg hν (abs_nonneg z))) ih

theorem difference_clipped_bound {f f' : ℝ → ℝ} {A ν : ℝ}
    (hA : 0 ≤ A) (hν : 0 ≤ ν)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hbound : ∀ x, |f x| ≤ A) (hderiv : ∀ x, |f' x| ≤ A*ν) (z x : ℝ) :
    |difference z f x| ≤ 2*A*min 1 (ν*|z|) := by
  have hlarge : |difference z f x| ≤ 2*A := by
    exact (abs_sub _ _).trans (by linarith [hbound (x+z), hbound x])
  have hsmall : |difference z f x| ≤ A*ν*|z| := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s:=Set.univ) (f:=f) (f':=f') (C:=A*ν)
      (fun y _ => (hf y).hasDerivWithinAt)
      (fun y _ => by simpa only [Real.norm_eq_abs] using hderiv y)
      convex_univ (Set.mem_univ x) (Set.mem_univ (x+z))
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, difference] using hh
  by_cases hz : ν*|z| ≤ 1
  · rw [min_eq_right hz]
    nlinarith [mul_nonneg hA (mul_nonneg hν (abs_nonneg z))]
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hz))]
    simpa using hlarge

/-- Translation differences commute with every level of a genuine
derivative tower. No formal derivative of a rough coefficient occurs. -/
theorem mixed_hasDerivAt (f : ℕ → ℝ → ℝ)
    (hf : ∀ k x, HasDerivAt (f k) (f (k+1) x) x) (zs : List ℝ) :
    ∀ k x, HasDerivAt (mixed zs (f k)) (mixed zs (f (k+1)) x) x := by
  induction zs with
  | nil => exact hf
  | cons z zs ih =>
    intro k x
    change HasDerivAt (fun y : ℝ => mixed zs (f k) (y+z)-mixed zs (f k) y)
      (mixed zs (f (k+1)) (x+z)-mixed zs (f (k+1)) x) x
    convert (((ih k (x+z)).comp_add_const x z).fun_sub (ih k x)) using 1

/-- Full all-order clipped Bernstein difference bound. It follows
from actual derivatives and their uniform bounds, for arbitrary signed
increments and every finite order. -/
theorem mixed_clipped_bound (f : ℕ → ℝ → ℝ) {A ν : ℝ}
    (hA : 0 ≤ A) (hν : 0 ≤ ν)
    (hf : ∀ k x, HasDerivAt (f k) (f (k+1) x) x)
    (hb : ∀ k x, |f k x| ≤ A*ν^k) (zs : List ℝ) :
    ∀ k x, |mixed zs (f k) x| ≤ 2^zs.length*A*ν^k*clips ν zs := by
  induction zs with
  | nil => intro k x; simpa [mixed,clips] using hb k x
  | cons z zs ih =>
    intro k x
    have hbase : 0 ≤ 2^zs.length*A*ν^k*clips ν zs := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA) (pow_nonneg hν _)) (clips_nonneg hν zs)
    have hd : ∀ y, |mixed zs (f (k+1)) y| ≤ (2^zs.length*A*ν^k*clips ν zs)*ν := by
      intro y
      convert ih (k+1) y using 1
      rw [pow_succ]
      ring
    have hh := difference_clipped_bound hbase hν (mixed_hasDerivAt f hf zs k)
      (ih k) hd z x
    calc
      _ ≤ 2*(2^zs.length*A*ν^k*clips ν zs)*min 1 (ν*|z|) := hh
      _ = _ := by
        simp only [List.length_cons, pow_succ, clips, List.map_cons, List.prod_cons]
        ring

/-- Weakening one additional clip gives the paired root slot with
exactly one fractional current-state input. -/
theorem paired_mixed_bound (f : ℕ → ℝ → ℝ) {A ν χ : ℝ}
    (hA : 0 ≤ A) (hν : 0 ≤ ν) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hf : ∀ k x, HasDerivAt (f k) (f (k+1) x) x)
    (hb : ∀ k x, |f k x| ≤ A*ν^k) (zs : List ℝ) (e x : ℝ) :
    |mixed (e::zs) (f 0) x| ≤
      2^(zs.length+1)*A*(min 1 (ν*|e|))^χ*clips ν zs := by
  have hc0 : 0 ≤ min 1 (ν*|e|) := le_min (by norm_num) (mul_nonneg hν (abs_nonneg e))
  have hc1 : min 1 (ν*|e|) ≤ 1 := min_le_left _ _
  have hweak : min 1 (ν*|e|) ≤ (min 1 (ν*|e|))^χ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hc0 hc1 hχ0 hχ1
  have hh := mixed_clipped_bound f hA hν hf hb (e::zs) 0 x
  simp only [List.length_cons, pow_zero, mul_one, clips, List.map_cons, List.prod_cons] at hh
  have hmult : 0 ≤ 2^(zs.length+1)*A*clips ν zs := by
    exact mul_nonneg (mul_nonneg (by positivity) hA) (clips_nonneg hν zs)
  have hw := mul_le_mul_of_nonneg_left hweak hmult
  change |mixed (e::zs) (f 0) x| ≤
    2^(zs.length+1)*A*(min 1 (ν*|e|)*clips ν zs) at hh
  nlinarith only [hh,hw]

/-- The derivative commutation uses only the finite number of
derivatives actually present in the fixed word. -/
theorem mixed_hasDerivAt_finite (f : ℕ → ℝ → ℝ) (N : ℕ)
    (hf : ∀ k, k<N → ∀ x, HasDerivAt (f k) (f (k+1) x) x) (zs : List ℝ) :
    ∀ k, k+zs.length<N → ∀ x,
      HasDerivAt (mixed zs (f k)) (mixed zs (f (k+1)) x) x := by
  induction zs with
  | nil => intro k hk x; exact hf k (by simpa using hk) x
  | cons z zs ih =>
    intro k hk x
    have hk' : k+zs.length<N := by simp only [List.length_cons] at hk; omega
    change HasDerivAt (fun y : ℝ => mixed zs (f k) (y+z)-mixed zs (f k) y)
      (mixed zs (f (k+1)) (x+z)-mixed zs (f (k+1)) x) x
    convert (((ih k hk' (x+z)).comp_add_const x z).fun_sub (ih k hk' x)) using 1

/-- Fixed-order clipped Bernstein bounds require no constant uniform
in the word order and no infinite derivative tower. -/
theorem mixed_clipped_bound_finite (f : ℕ → ℝ → ℝ) {A ν : ℝ} (N : ℕ)
    (hA : 0 ≤ A) (hν : 0 ≤ ν)
    (hf : ∀ k, k<N → ∀ x, HasDerivAt (f k) (f (k+1) x) x)
    (hb : ∀ k, k≤N → ∀ x, |f k x| ≤ A*ν^k) (zs : List ℝ) :
    ∀ k, k+zs.length≤N → ∀ x,
      |mixed zs (f k) x| ≤ 2^zs.length*A*ν^k*clips ν zs := by
  induction zs with
  | nil => intro k hk x; simpa [mixed,clips] using hb k (by simpa using hk) x
  | cons z zs ih =>
    intro k hk x
    have hk' : k+zs.length<N := by simp only [List.length_cons] at hk; omega
    have hbase : 0 ≤ 2^zs.length*A*ν^k*clips ν zs := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA) (pow_nonneg hν _)) (clips_nonneg hν zs)
    have hd : ∀ y, |mixed zs (f (k+1)) y| ≤ (2^zs.length*A*ν^k*clips ν zs)*ν := by
      intro y
      convert ih (k+1) (by omega) y using 1
      rw [pow_succ]
      ring
    have hh := difference_clipped_bound hbase hν (mixed_hasDerivAt_finite f N hf zs k hk')
      (ih k (by omega)) hd z x
    calc
      _ ≤ 2*(2^zs.length*A*ν^k*clips ν zs)*min 1 (ν*|z|) := hh
      _ = _ := by
        simp only [List.length_cons,pow_succ,clips,List.map_cons,List.prod_cons]
        ring

end SHE.FiniteDifferences
