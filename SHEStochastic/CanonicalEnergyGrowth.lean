module

public import SHEStochastic.ContinuousCanonicalCompensator
public import SHEStochastic.CanonicalLinearFluctuation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.CanonicalEnergyGrowth
open MeasureTheory SHE StoppedPathPasting PastedGeneratorFunctional
open scoped NNReal
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] [DecidableEq ι]

/-- Time integration preserves linear full-path-energy growth. -/
theorem path_integral (H : ℝ≥0) (w : BoundedContinuousFunction ℝ ℝ) (b : C(E,ℝ))
    (B : ℝ) (hB : 0≤B) (hb : ∀ z,‖b z‖≤B*(1+‖z‖^2))
    (x : Path H E) (t : Time H) :
    ‖ContinuousPathIntegral.value H w b x t‖≤(‖w‖*B*(H : ℝ))*(1+‖x‖^2) := by
  have hpoint (s : ℝ) : ‖w s*b (read H x s)‖≤(‖w‖*B)*(1+‖x‖^2) := by
    have hr : ‖read H x s‖≤‖x‖ := x.norm_coe_le_norm _
    have hr2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    rw [norm_mul]
    apply (mul_le_mul (w.norm_coe_le_norm s) (hb (read H x s)) (norm_nonneg _) (norm_nonneg _)).trans
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg w) hB) (sub_nonneg.mpr hr2)]
  have ht : |t.val-0|≤H := by
    rw [sub_zero,abs_of_nonneg t.property.1]
    exact t.property.2
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hpoint s)).trans
  calc
    ((‖w‖*B)*(1+‖x‖^2))*|t.val-0|≤((‖w‖*B)*(1+‖x‖^2))*(H : ℝ) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

theorem compensator (H : ℝ≥0) (rate : ℝ) (hrate : 0≤rate) (b : C(E,ℝ))
    (B : ℝ) (hB : 0≤B) (hb : ∀ z,‖b z‖≤B*(1+‖z‖^2)) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    ‖ContinuousCanonicalCompensator.value H rate hrate b t x‖≤
      (‖PathIntegratedCovariance.exponential H rate hrate‖*B*(H : ℝ))*(1+‖x.1‖^2) :=
  path_integral H _ b B hB hb x.1 (AdaptedCanonicalPathTests.clock H t)

/-- A Fourier fluctuation grows at most linearly in the full state
path norm, uniformly over observation times. -/
theorem fluctuation (H : ℝ≥0) (L : E →L[ℝ] ℝ) (rate : ℝ) (hrate : 0≤rate) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    ‖CanonicalLinearFluctuation.value H L rate t x‖≤
      ((Real.exp ((H : ℝ)*rate)+1)*‖L‖)*‖x.1‖ := by
  have hb (q : Time H) : ‖L (x.1 q)‖≤‖L‖*‖x.1‖ :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (x.1.norm_coe_le_norm q) (norm_nonneg _))
  have hexp : Real.exp ((min t H : ℝ≥0)*rate)≤Real.exp ((H : ℝ)*rate) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right t H) hrate)
  change ‖Real.exp ((min t H : ℝ≥0)*rate)*L (x.1 (CanonicalStateDriverFiltration.clock H t))-
    L (x.1 (origin H))‖≤_
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply (add_le_add
    (mul_le_mul hexp (hb _) (norm_nonneg _) (Real.exp_pos _).le) (hb _)).trans_eq
  ring

theorem square_fluctuation (H : ℝ≥0) (L : E →L[ℝ] ℝ) (rate : ℝ) (hrate : 0≤rate) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    ‖CanonicalLinearFluctuation.value H L rate t x‖^2≤
      (((Real.exp ((H : ℝ)*rate)+1)*‖L‖)^2)*‖x.1‖^2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (fluctuation H L rate hrate t x) 2

end SHEStochastic.CanonicalEnergyGrowth
