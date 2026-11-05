module

public import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.AEContinuousIntervalClosure
open MeasureTheory ProbabilityTheory Filter Set

/-- Continuous modifications equal at every deterministic time of a
half-open interval agree simultaneously on its closed interval. This
handles the terminal endpoint without new stochastic estimates. -/
theorem ae_eq_Icc {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    (μ : Measure Ω) (f g : ℝ → Ω → E)
    (hf : ∀ ω, Continuous (fun t ↦ f t ω)) (hg : ∀ ω, Continuous (fun t ↦ g t ω))
    (a b : ℝ) (hab : a < b) (he : ∀ t ∈ Ico a b, f t =ᵐ[μ] g t) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc a b, f t ω = g t ω := by
  have hcF : ∀ᵐ ω ∂μ, Continuous (fun t : Ico a b ↦ f t.val ω) :=
    Eventually.of_forall fun ω ↦ (hf ω).comp continuous_subtype_val
  have hcG : ∀ᵐ ω ∂μ, Continuous (fun t : Ico a b ↦ g t.val ω) :=
    Eventually.of_forall fun ω ↦ (hg ω).comp continuous_subtype_val
  have hh := indistinguishable_of_edist_modification hcF hcG
    (fun t ↦ (he t.val t.property).mono fun _ h ↦ edist_eq_zero.mpr h)
  filter_upwards [hh] with ω hω t ht
  have hs : Ico a b ⊆ {s | f s ω = g s ω} := fun s hs ↦ edist_eq_zero.mp (hω ⟨s, hs⟩)
  have hc := isClosed_eq (hf ω) (hg ω)
  have hclose := hc.closure_subset_iff.mpr hs
  rw [closure_Ico (ne_of_lt hab)] at hclose
  exact hclose ht

end SHEStochastic.AEContinuousIntervalClosure
