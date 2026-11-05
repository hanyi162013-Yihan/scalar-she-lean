module

public import SHE.LpDominatedLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.LpCrossDominatedLimit
open MeasureTheory Filter
open scoped ENNReal Topology
variable {X E D : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup D] [InnerProductSpace ℝ D] {μ : Measure X}

/-- Hilbert L² dominated convergence with a scalar or other Hilbert
dominator. No separability of the whole L² probability space is needed. -/
theorem tendsto (v : Lp D 2 μ) (g : Lp E 2 μ) (f : ℕ→Lp E 2 μ)
    (hf : ∀ n,∀ᵐ x ∂μ,‖f n x‖≤‖v x‖) (hg : ∀ᵐ x ∂μ,‖g x‖≤‖v x‖)
    (hlim : ∀ᵐ x ∂μ,Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  let e : ℕ→ℝ := fun n => ∫ x,‖f n x-g x‖^2 ∂μ
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun x => 4*‖v x‖^2)
    (F := fun n x => ‖f n x-g x‖^2) (f := fun _ => (0:ℝ))
    (Eventually.of_forall (fun n => ((Lp.stronglyMeasurable (f n)).sub (Lp.stronglyMeasurable g)).norm.pow 2
      |>.aestronglyMeasurable))
    (Eventually.of_forall (fun n => by
      filter_upwards [hf n,hg] with x hx hy
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have ht := (norm_sub_le (f n x) (g x)).trans (add_le_add hx hy)
      nlinarith [norm_nonneg (f n x-g x)]))
    ((Lp.memLp v).norm.integrable_sq.const_mul 4)
    (hlim.mono (fun x hx => by
      have hh := (hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2
      simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using hh))
  have he : Tendsto e atTop (𝓝 0) := by simpa only [e,integral_zero] using hi
  apply KernelEnergyCauchy.tendsto_of_energy_error f g (fun n => ENNReal.ofReal (e n))
    (by simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp he)
  intro n
  apply le_of_eq
  congr 1
  rw [PredictableL2.realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (f n) g] with x hx
  rw [hx]
  rfl

end SHE.LpCrossDominatedLimit
