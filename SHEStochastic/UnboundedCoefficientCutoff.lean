module

public import SHEStochastic.BallProjection
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedCoefficientCutoff
open Metric
open scoped NNReal

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

def coefficient (G : E → V) (R : ℝ≥0) : E → V := G ∘ BallProjection.project R

theorem agrees (G : E → V) (R : ℝ≥0) {x : E} (hx : ‖x‖ ≤ R) :
    coefficient G R x = G x := by
  simp only [coefficient, Function.comp_apply, BallProjection.of_norm_le R hx]

/-- The cutoff preserves the exact global Hölder seminorm and exponent. -/
theorem holder {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (R : ℝ≥0) :
    HolderWith C β (coefficient G R) := by
  simpa only [coefficient, NNReal.one_rpow, mul_one] using hG.comp (BallProjection.lipschitz R).holderWith

theorem norm_le_origin_add {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (x : E) :
    ‖G x‖ ≤ ‖G 0‖ + (C : ℝ) * ‖x‖ ^ (β : ℝ) := by
  have hh := hG.dist_le x 0
  simp only [dist_eq_norm, sub_zero] at hh
  calc
    _ = ‖(G x - G 0) + G 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖G x - G 0‖ + ‖G 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- A cutoff-independent growth constant, for matrix or scalar output. -/
theorem growth {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (R : ℝ≥0) (x : E) :
    ‖coefficient G R x‖ ≤ (‖G 0‖ + (C : ℝ)) * (1 + ‖x‖ ^ (β : ℝ)) := by
  have hh := norm_le_origin_add hG (BallProjection.project R x)
  have hp := Real.rpow_le_rpow (norm_nonneg (BallProjection.project R x))
    (BallProjection.norm_le R x) β.property
  have hpow := Real.rpow_nonneg (norm_nonneg x) (β : ℝ)
  change ‖G (BallProjection.project R x)‖ ≤ _
  calc
    _ ≤ ‖G 0‖ + (C : ℝ) * ‖BallProjection.project R x‖ ^ (β : ℝ) := hh
    _ ≤ ‖G 0‖ + (C : ℝ) * ‖x‖ ^ (β : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp C.property)
    _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg (G 0)) hpow, C.property]

/-- At each fixed radius the coefficient is bounded everywhere. -/
theorem bounded {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (R : ℝ≥0) (x : E) :
    ‖coefficient G R x‖ ≤ ‖G 0‖ + (C : ℝ) * (R : ℝ) ^ (β : ℝ) := by
  have hh := norm_le_origin_add hG (BallProjection.project R x)
  have hp := Real.rpow_le_rpow (norm_nonneg (BallProjection.project R x))
    (BallProjection.norm_le_radius R x) β.property
  change ‖G (BallProjection.project R x)‖ ≤ _
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp C.property))

theorem original_growth {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (x : E) :
    ‖G x‖ ≤ (‖G 0‖ + (C : ℝ)) * (1 + ‖x‖ ^ (β : ℝ)) := by
  have hh := growth hG ‖x‖₊ x
  rwa [agrees G ‖x‖₊ le_rfl] at hh

/-- The squared coefficient has precisely the sublinear energy growth
used in the stochastic heat-row estimate, also for matrix output. -/
theorem squared_growth {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (x : E) :
    ‖G x‖ ^ 2 ≤ 2 * (‖G 0‖ + (C : ℝ)) ^ 2 * (1 + ‖x‖ ^ (2 * (β : ℝ))) := by
  let A := ‖G 0‖ + (C : ℝ)
  let z := ‖x‖ ^ (β : ℝ)
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) C.property
  have hz : 0 ≤ z := Real.rpow_nonneg (norm_nonneg _) _
  have hb : ‖G x‖ ≤ A * (1 + z) := original_growth hG x
  have hs := pow_le_pow_left₀ (norm_nonneg (G x)) hb 2
  have he : ‖x‖ ^ (2 * (β : ℝ)) = z ^ 2 := by
    dsimp [z]
    rw [← Real.rpow_mul_natCast (norm_nonneg x)]
    congr 1
    ring
  rw [he]
  change ‖G x‖ ^ 2 ≤ 2 * A ^ 2 * (1 + z ^ 2)
  nlinarith [sq_nonneg (A * (z - 1))]

/-- A global nondegeneracy condition on coefficient values survives
unchanged: the cutoff only changes the state at which G is evaluated. -/
theorem preserves {G : E → V} (P : V → Prop) (hG : ∀ x, P (G x)) (R : ℝ≥0) :
    ∀ x, P (coefficient G R x) := fun x ↦ hG (BallProjection.project R x)

end SHEStochastic.UnboundedCoefficientCutoff
