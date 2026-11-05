module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.SquaredIncrementContinuity
open Filter
open scoped Topology

/-- A shared continuity step for predictable-input Hilbert families.
Only the proved squared increment estimate is needed. -/
theorem continuous {A E : Type*} [PseudoMetricSpace A] [NormedAddCommGroup E]
    (f : A → E) (C q : ℝ) (hq : 0<q)
    (hb : ∀ p r, ‖f p-f r‖^2≤C*dist p r^q) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro r
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hd : Continuous (fun p : A ↦ dist p r^q) :=
    (continuous_id.dist continuous_const).rpow_const (fun _ ↦ Or.inr hq.le)
  have hcap : Tendsto (fun p : A ↦ C*dist p r^q) (𝓝 r) (𝓝 0) := by
    have hc : Continuous (fun p : A ↦ C*dist p r^q) := continuous_const.mul hd
    have hh := hc.tendsto r
    change Tendsto (fun p : A ↦ C*dist p r^q) (𝓝 r) (𝓝 (C*dist r r^q)) at hh
    simpa only [dist_self,Real.zero_rpow hq.ne',mul_zero] using hh
  have hs := squeeze_zero (fun p : A ↦ sq_nonneg ‖f p-f r‖) (fun p ↦ hb p r) hcap
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun p : A ↦ Real.sqrt (‖f p-f r‖^2)) (𝓝 r) (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

end SHEStochastic.SquaredIncrementContinuity
