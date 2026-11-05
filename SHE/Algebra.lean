module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-! Exact identities used by the controlled coupling and stopped expansion.
These theorems do not assert existence or estimates for the stochastic fields. -/
noncomputable section
namespace SHE
open Finset

/-- Noise-row difference in the joint coordinate, at an arbitrary endpoint. -/
theorem joint_row_difference {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u v : E) (e : ℝ) : u - (v + (1 - e) • (u - v)) = e • (u - v) := by
  module

/-- The terminal value of the backward joint coordinate is exactly V. -/
theorem joint_terminal {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u v : E) : u - (1 : ℝ) • (u - v) = v := by simp

/-- Algebraic cancellation of the coupling drift after heat transport.
The common heat drift has already been removed. -/
theorem joint_drift_cancellation (Λ e d : ℝ) :
    0 - (Λ * e * d + e * (-Λ * d)) = 0 := by ring

/-- A deterministic derivative version of the same cancellation. -/
theorem backward_coordinate_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u d : ℝ → E} {e : ℝ → ℝ} {t Λ : ℝ}
    (hu : HasDerivAt u (0 : E) t)
    (hd : HasDerivAt d ((-Λ) • d t) t)
    (he : HasDerivAt e (Λ * e t) t) :
    HasDerivAt (fun s => u s - e s • d s) 0 t := by
  have hz : (0 : E) - (e t • ((-Λ) • d t) + (Λ * e t) • d t) = 0 := by module
  simpa only [hz] using hu.fun_sub (he.fun_smul hd)

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x "," y "⟫" => inner ℝ x y

/-- The direct joint bracket defect, retaining both cross terms. -/
theorem direct_bracket_defect (vi vj bi bj : E) (ri rj : ℝ) :
    ⟪vi + ri • bi, vj + rj • bj⟫ - ⟪vi, vj⟫ =
      ri * ⟪bi, vj⟫ + rj * ⟪vi, bj⟫ + ri * rj * ⟪bi, bj⟫ := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The manuscript's signed/quadratic/skew decomposition is an exact identity. -/
theorem three_bracket_defects (ui uj vi vj : E) (ei ej : ℝ) :
    (1 - ei) * ⟪ui - vi, vj⟫ + (1 - ej) * ⟪vi, uj - vj⟫ +
      (1 - ei) * (1 - ej) * ⟪ui - vi, uj - vj⟫ =
    (1 - (ei + ej) / 2) * (⟪ui, uj⟫ - ⟪vi, vj⟫) -
      ((ei + ej) / 2 - ei * ej) * ⟪ui - vi, uj - vj⟫ +
      (ei - ej) / 2 * (⟪ui, uj - vj⟫ - ⟪ui - vi, uj⟫) := by
  simp only [inner_sub_left, inner_sub_right]
  ring

end InnerProduct

/-- An abstract finite recursive expansion. The J term is the first defect
at that level; it is not recursively expanded by this identity. -/
structure FiniteExpansion where
  R : ℕ → ℝ
  C : ℕ → ℝ
  N : ℕ → ℝ
  J : ℕ → ℝ
  step : ∀ n, R n = C n + N n + J n + R (n + 1)

theorem FiniteExpansion.prefix (E : FiniteExpansion) (n : ℕ) :
    E.R 0 = (∑ j ∈ range n, (E.C j + E.N j + E.J j)) + E.R n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hs := E.step n
    linarith

/-- Subtraction of two complete expansions. No stochastic estimate is hidden here. -/
theorem FiniteExpansion.compare (U V : FiniteExpansion) (n : ℕ) :
    U.R 0 - V.R 0 =
      (∑ j ∈ range n, ((U.C j - V.C j) + (U.N j - V.N j))) +
      (U.R n - V.R n) + (∑ j ∈ range n, (U.J j - V.J j)) := by
  rw [U.prefix n, V.prefix n]
  simp only [sum_add_distrib, sum_sub_distrib]
  ring

/-- In the ordinary U expansion J=0; V's first-hit marks have a minus sign. -/
theorem FiniteExpansion.compare_first_hit (U V : FiniteExpansion)
    (hU : ∀ j, U.J j = 0) (n : ℕ) :
    U.R 0 - V.R 0 =
      (∑ j ∈ range n, ((U.C j - V.C j) + (U.N j - V.N j))) +
      (U.R n - V.R n) - (∑ j ∈ range n, V.J j) := by
  rw [U.compare V n]
  simp [hU, sum_neg_distrib, sub_eq_add_neg]

/-- The excluded first pair must be regrouped with its reference martingale. -/
theorem first_pair_regroup (CU CV NU NV XU XV : ℝ) :
    (CU - CV) + (NU - NV) =
      (XU - XV) + ((NU - (XU - CU)) - (NV - (XV - CV))) := by ring

/-- Absorption retains both linear slots of the manuscript's master inequality. -/
theorem absorb_two_linear_slots {K m a b s F : ℝ}
    (hK : K ≤ a * K + b * m + F) (hm : m ≤ s * K)
    (hb : 0 ≤ b) (hsmall : a + b * s ≤ 1 / 2) (hK0 : 0 ≤ K) :
    K ≤ 2 * F := by
  have hbm := mul_le_mul_of_nonneg_left hm hb
  have hc := mul_le_mul_of_nonneg_right hsmall hK0
  nlinarith

end SHE
