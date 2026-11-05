module

public import SHE.UncutHistoryMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.DominatedCutoffLimit
open Set MeasureTheory Filter Topology
variable {Q : Type*} [MeasurableSpace Q] (μ : Measure Q)

/-- A history-dependent positive gap is sufficient for an actual
cutoff integral limit when its common uncut weight is integrable. -/
theorem integral_tendsto {W f : Q→ℝ} {F : ℝ→Q→ℝ} {M : ℝ}
    (hW : Integrable W μ)
    (hFm : ∀ δ>0,Measurable (F δ)) (hF : ∀ δ>0,∀ q,‖F δ q‖≤M*W q)
    (hEq : ∀ q,∃ η : ℝ,0<η ∧ ∀ δ>0,δ<η→F δ q=f q) :
    Tendsto (fun δ : ℝ => ∫ q,F δ q ∂μ) (𝓝[>] (0:ℝ)) (𝓝 (∫ q,f q ∂μ)) := by
  have ht (q : Q) : Tendsto (fun δ : ℝ => F δ q) (𝓝[>] (0:ℝ)) (𝓝 (f q)) := by
    obtain ⟨η,hη,hEq⟩ := hEq q
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds] with δ hδ hd
    exact (hEq δ hδ hd).symm
  exact tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun q => M*W q)
    (by filter_upwards [self_mem_nhdsWithin] with δ hδ; exact (hFm δ hδ).aestronglyMeasurable)
    (by filter_upwards [self_mem_nhdsWithin] with δ hδ; exact Eventually.of_forall (hF δ hδ))
    (hW.const_mul M) (Eventually.of_forall ht)

theorem integral_abs_sub_tendsto_zero {W f : Q→ℝ} {F : ℝ→Q→ℝ} {M : ℝ}
    (hW : Integrable W μ)
    (hfm : Measurable f) (hFm : ∀ δ>0,Measurable (F δ))
    (hf : ∀ q,‖f q‖≤M*W q) (hF : ∀ δ>0,∀ q,‖F δ q‖≤M*W q)
    (hEq : ∀ q,∃ η : ℝ,0<η ∧ ∀ δ>0,δ<η→F δ q=f q) :
    Tendsto (fun δ : ℝ => ∫ q,|F δ q-f q| ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := integral_tendsto μ (M := 2*M) (f := fun _ => (0:ℝ)) (F := fun δ q => |F δ q-f q|) hW
    (fun δ hδ => ((hFm δ hδ).sub hfm).norm)
    (fun δ hδ q => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hF δ hδ q) (hf q)).trans_eq (by ring)))
    (fun q => by
      obtain ⟨η,hη,heq⟩ := hEq q
      exact ⟨η,hη,fun δ hδ hd => by rw [heq δ hδ hd,sub_self,abs_zero]⟩)
  simpa only [integral_zero] using ht

end SHE.DominatedCutoffLimit
