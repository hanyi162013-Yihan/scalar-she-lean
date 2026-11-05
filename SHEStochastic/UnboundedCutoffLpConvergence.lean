module

public import SHEStochastic.HolderWeightedEnergy
public import SHEStochastic.UnboundedCutoffConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.UnboundedCutoffLpConvergence
open MeasureTheory Filter
open scoped NNReal Topology
variable {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0}

/-- A cutoff-independent integrable majorant for the coefficient error.
It needs only L2 state data, without a pointwise bound on the state. -/
theorem squared_error_bound (hG : HolderWith C β G) (hβ1 : β≤1) (R : ℝ≥0) (x : E) :
    ‖UnboundedCoefficientCutoff.coefficient G R x-G x‖^2≤(C : ℝ)^2*(1+4*‖x‖^2) := by
  let δ : ℝ := ‖BallProjection.project R x-x‖
  have hδ : 0≤δ := norm_nonneg _
  have hd : δ≤2*‖x‖ := (norm_sub_le _ _).trans (by
    have hp := BallProjection.norm_le R x
    linarith)
  have hp : δ^(2*(β : ℝ))≤1+δ^2 := by
    by_cases h : δ≤1
    · exact (Real.rpow_le_one hδ h (by positivity)).trans (by linarith [sq_nonneg δ])
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h)
        (show 2*(β : ℝ)≤(2 : ℝ) from by
          have hb : (β : ℝ)≤1 := by exact_mod_cast hβ1
          linarith)
      rw [Real.rpow_two] at hh
      linarith
  have he : ‖UnboundedCoefficientCutoff.coefficient G R x-G x‖≤(C : ℝ)*δ^(β : ℝ) := by
    simpa only [UnboundedCoefficientCutoff.coefficient,Function.comp_apply,dist_eq_norm] using
      hG.dist_le (BallProjection.project R x) x
  have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
  rw [mul_pow,←Real.rpow_mul_natCast hδ] at hs
  have hmul : (β : ℝ)*(2 : ℕ)=2*(β : ℝ) := by push_cast;ring
  rw [hmul] at hs
  have hd2 : δ^2≤4*‖x‖^2 := by
    have hh := pow_le_pow_left₀ hδ hd 2
    nlinarith
  exact hs.trans ((mul_le_mul_of_nonneg_left hp (sq_nonneg (C : ℝ))).trans
    (mul_le_mul_of_nonneg_left (by linarith : 1+δ^2≤1+4*‖x‖^2) (sq_nonneg _)))

/-- Radial coefficient truncations converge in spatial L2 at every
L2 state, including states with unbounded pointwise representatives. -/
theorem energy_tendsto (ν : Measure X) [IsFiniteMeasure ν]
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1) (u : Lp E 2 ν) :
    Tendsto (fun m : ℕ => ∫ x,‖UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0) (u x)-G (u x)‖^2 ∂ν)
      atTop (𝓝 0) := by
  have hi : Integrable (fun x => (C : ℝ)^2*(1+4*‖u x‖^2)) ν :=
    ((integrable_const (1 : ℝ)).add (((Lp.memLp u).norm.integrable_sq).const_mul 4)).const_mul _
  have hm (m : ℕ) : AEStronglyMeasurable
      (fun x => ‖UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0) (u x)-G (u x)‖^2) ν :=
    ((((UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)).continuous hβ).sub (hG.continuous hβ)).comp_aestronglyMeasurable
      (Lp.stronglyMeasurable u).aestronglyMeasurable).norm.pow 2
  have hl : ∀ x,Tendsto (fun m : ℕ =>
      ‖UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0) (u x)-G (u x)‖^2) atTop (𝓝 (0 : ℝ)) := by
    intro x
    have hh := UnboundedCutoffConvergence.eventually_eqOn G (s := {u x}) (Bornology.isBounded_singleton)
    apply tendsto_const_nhds.congr'
    filter_upwards [hh] with m hm
    simp only [hm (Set.mem_singleton _),sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)]
  have hd := tendsto_integral_of_dominated_convergence
    (fun x => (C : ℝ)^2*(1+4*‖u x‖^2)) hm hi
    (fun m => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact squared_error_bound hG hβ1 (m : ℝ≥0) (u x))
    (Filter.Eventually.of_forall hl)
  simpa only [integral_zero] using hd

end SHEStochastic.UnboundedCutoffLpConvergence
