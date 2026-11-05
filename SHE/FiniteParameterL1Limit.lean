module

public import SHE.PastParameterHistoryExpectation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteParameterL1Limit
open Set MeasureTheory Filter Topology
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- A genuine dominated-convergence lemma for an actual moving family.
Both measurability and the uniform bound are used under the original
finite sample/history measure. -/
theorem bounded_continuous_L1 (g : ℝ≥0→Ω→ℝ)
    (hm : ∀ ε,AEStronglyMeasurable (g ε) μ) {C : ℝ} (hb : ∀ ε ω,‖g ε ω‖≤C)
    (hc : ∀ ω,Continuous (fun ε : ℝ≥0 => g ε ω)) :
    Tendsto (fun ε : ℝ => ∫ ω,|g ε.toNNReal ω-g 0 ω| ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht (ω : Ω) : Tendsto (fun ε : ℝ => |g ε.toNNReal ω-g 0 ω|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := ((((hc ω).comp continuous_real_toNNReal).tendsto (0:ℝ)).sub_const (g 0 ω)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun _ => 2*C)
    (Eventually.of_forall (fun ε : ℝ => ((hm ε.toNNReal).sub (hm 0)).norm))
    (Eventually.of_forall (fun ε : ℝ => ae_of_all _ (fun ω => by
      simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_abs] using
        (norm_sub_le (g ε.toNNReal ω) (g 0 ω)).trans ((add_le_add (hb ε.toNNReal ω) (hb 0 ω)).trans_eq (by ring)))))
    (integrable_const _) (ae_of_all _ ht)
  simpa only [integral_zero,Pi.sub_apply,Real.norm_eq_abs] using hi

theorem bounded_continuous_integral (g : ℝ≥0→Ω→ℝ)
    (hm : ∀ ε,AEStronglyMeasurable (g ε) μ) {C : ℝ} (hb : ∀ ε ω,‖g ε ω‖≤C)
    (hc : ∀ ω,Continuous (fun ε : ℝ≥0 => g ε ω)) :
    Tendsto (fun ε : ℝ => ∫ ω,g ε.toNNReal ω ∂μ) (𝓝[>] (0:ℝ)) (𝓝 (∫ ω,g 0 ω ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun (ε : ℝ) ω => g ε.toNNReal ω) (f := g 0) (l := 𝓝[>] (0:ℝ)) (fun _ => C)
    (Eventually.of_forall (fun ε : ℝ => hm ε.toNNReal))
    (Eventually.of_forall (fun ε : ℝ => ae_of_all _ (hb ε.toNNReal))) (integrable_const _)
  apply ae_of_all
  intro ω
  have hh := ((hc ω).comp continuous_real_toNNReal).tendsto (0:ℝ)
  simpa only [Function.comp_def,Real.toNNReal_zero] using hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))

end SHE.FiniteParameterL1Limit
