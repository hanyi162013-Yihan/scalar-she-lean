module

public import SHEStochastic.WeakLimitMomentTests
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.EnergyClipping
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem clip_norm {E : Type*} [TopologicalSpace E] (f : E → ℝ) (hf : Continuous f)
    (R : ℝ) (hR : 0≤R) (x : E) : ‖WeakLimitMomentTests.clip f hf R hR x‖≤R := by
  change |max (-R) (min R (f x))|≤R
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

/-- Scalar clipping never enlarges the absolute truncation error
beyond the original absolute value. -/
theorem scalar_error (x R : ℝ) (hR : 0≤R) :
    |x-max (-R) (min R x)|≤|x| := by
  by_cases hl : x< -R
  · rw [min_eq_right (by linarith),max_eq_left hl.le,
      abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · by_cases hh : R<x
    · rw [min_eq_left hh.le,max_eq_right (by linarith),
        abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_right (le_of_not_gt hh),max_eq_right (le_of_not_gt hl),sub_self,abs_zero]
      exact abs_nonneg _

/-- A test of linear energy growth has clipping error supported on
the energy tail. Taking a threshold at least one absorbs the constant. -/
theorem pointwise (x e C R : ℝ) (hC : 0≤C) (hR : 1≤R)
    (hx : |x|≤C*(1+e)) :
    ENNReal.ofReal |x-max (-(C*(1+R))) (min (C*(1+R)) x)|≤
      (if R≤e then ENNReal.ofReal (2*C)*ENNReal.ofReal e else 0) := by
  have ht : 0≤C*(1+R) := mul_nonneg hC (by linarith)
  by_cases he : R≤e
  · rw [if_pos he]
    apply (ENNReal.ofReal_le_ofReal ((scalar_error x _ ht).trans hx)).trans
    rw [←ENNReal.ofReal_mul (by positivity : 0≤2*C)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  · rw [if_neg he]
    have hxe : |x|≤C*(1+R) := hx.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    have hh := abs_le.mp hxe
    rw [min_eq_right hh.2,max_eq_right hh.1,sub_self,abs_zero,ENNReal.ofReal_zero]

/-- The expectation error is bounded by the actual energy-tail
integral, with no second moment of the test function. -/
theorem integral_bound {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf : Continuous f)
    (hi : Integrable f μ) (energy : E → ℝ) (henergy : Measurable energy)
    (C R : ℝ) (hC : 0≤C) (hR : 1≤R) (hgrowth : ∀ x,|f x|≤C*(1+energy x)) :
    ENNReal.ofReal ‖(∫ x,f x ∂μ)-
      (∫ x,WeakLimitMomentTests.clip f hf (C*(1+R)) (by positivity) x ∂μ)‖≤
      ENNReal.ofReal (2*C)*(∫⁻ x in {x | R≤energy x},ENNReal.ofReal (energy x) ∂μ) := by
  let g := WeakLimitMomentTests.clip f hf (C*(1+R)) (by positivity)
  rw [←integral_sub hi (g.integrable μ),ofReal_norm]
  apply (enorm_integral_le_lintegral_enorm _).trans
  rw [←lintegral_const_mul'' _ (henergy.ennreal_ofReal.aemeasurable.restrict),
    ←lintegral_indicator (measurableSet_le measurable_const henergy)]
  apply lintegral_mono
  intro x
  simpa only [←ofReal_norm,Real.norm_eq_abs,g,WeakLimitMomentTests.clip,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup,Set.indicator_apply,Set.mem_setOf_eq] using
      pointwise (f x) (energy x) C R hC hR (hgrowth x)

/-- Tail integrals of any fixed integrable real energy vanish. -/
theorem tails_tendsto (μ : Measure Ω) (energy : Ω → ℝ) (hm : Measurable energy)
    (hi : Integrable energy μ) :
    Tendsto (fun R : ℕ => ∫⁻ x in {x | (R : ℝ)≤energy x},ENNReal.ofReal (energy x) ∂μ)
      atTop (𝓝 0) := by
  let F := fun R : ℕ => {x | (R : ℝ)≤energy x}.indicator (fun x => ENNReal.ofReal (energy x))
  have hmeas (R : ℕ) : Measurable (F R) :=
    hm.ennreal_ofReal.indicator (measurableSet_le measurable_const hm)
  have hdom (R : ℕ) : F R≤fun x => ENNReal.ofReal (energy x) := by
    intro x
    change ({x | (R : ℝ)≤energy x}.indicator (fun x => ENNReal.ofReal (energy x)) x)≤ENNReal.ofReal (energy x)
    by_cases hx : (R : ℝ)≤energy x
    · simp only [F,Set.indicator_apply,Set.mem_setOf_eq,hx,ite_true,le_refl]
    · simp only [Set.indicator_apply,Set.mem_setOf_eq,hx,ite_false]
      exact bot_le
  have hfin : (∫⁻ x,ENNReal.ofReal (energy x) ∂μ)≠⊤ :=
    ne_top_of_le_ne_top hi.hasFiniteIntegral.ne (lintegral_ofReal_le_lintegral_enorm _)
  have hpt (x : Ω) : Tendsto (fun R => F R x) atTop (𝓝 0) := by
    obtain ⟨N,hN⟩ := exists_nat_gt (energy x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with R hR
    have hRx : ¬(R : ℝ)≤energy x := by
      have hNR : (N : ℝ)≤R := by exact_mod_cast hR
      linarith
    simp only [F,Set.indicator_apply,Set.mem_setOf_eq,hRx,ite_false]
  have ht := tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (energy x)) hmeas
    (fun R => Filter.Eventually.of_forall (hdom R)) hfin (Filter.Eventually.of_forall hpt)
  simpa only [F,lintegral_indicator (measurableSet_le measurable_const hm),lintegral_zero] using ht

end SHEStochastic.EnergyClipping
