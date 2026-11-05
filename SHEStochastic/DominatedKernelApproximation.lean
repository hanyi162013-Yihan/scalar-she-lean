module

public import SHE.EnergyConvergence
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.DominatedKernelApproximation
open MeasureTheory Filter
open scoped ENNReal Topology
variable {X C : Type*} [MeasurableSpace X] [NormedAddCommGroup C] [SecondCountableTopology C]
    [MeasurableSpace C] [BorelSpace C] {μ : Measure X}

/-- The common dominated L2 kernel argument, independent of the
particular heat operator, spatial dimension or stochastic integral. -/
theorem energy_tendsto (r : X → C) (hr : Measurable r) (hmem : MemLp r 2 μ)
    (f : ℕ → X → C) (hf : ∀ n, Measurable (f n))
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖r x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (r x))) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖f n x-r x‖^2) ∂μ) atTop (𝓝 0) := by
  have hfin : (∫⁻ x, ENNReal.ofReal (‖r x‖^2) ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg ‖r x‖)).mp
      hmem.norm.integrable_sq.hasFiniteIntegral
  have hdom : (∫⁻ x, ENNReal.ofReal 4*ENNReal.ofReal (‖r x‖^2) ∂μ) ≠ ∞ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have he := tendsto_lintegral_of_dominated_convergence
    (fun x => ENNReal.ofReal 4*ENNReal.ofReal (‖r x‖^2))
    (F := fun n x => ENNReal.ofReal (‖f n x-r x‖^2)) (f := fun _ => 0)
    (fun n => ENNReal.continuous_ofReal.measurable.comp (((hf n).sub hr).norm.pow_const 2))
    (fun n => (hb n).mono fun x hx => by
      dsimp only
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [norm_sub_le (f n x) (r x),norm_nonneg (f n x-r x),norm_nonneg (r x)])
    hdom (ht.mono fun x hx => by
      have hs : Tendsto (fun n => f n x-r x) atTop (𝓝 (0 : C)) := by
        simpa only [sub_self] using hx.sub (tendsto_const_nhds (x := r x))
      have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.norm.pow 2)
      change Tendsto (fun n => ENNReal.ofReal (‖f n x-r x‖^2)) atTop
        (𝓝 (ENNReal.ofReal (‖(0 : C)‖^2))) at he
      simpa only [norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),ENNReal.ofReal_zero] using he)
  simpa only [lintegral_zero] using he

end SHEStochastic.DominatedKernelApproximation
