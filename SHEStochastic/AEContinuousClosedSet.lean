module

public import SHEStochastic.NativeVectorProjection

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.AEContinuousClosedSet
open MeasureTheory Set

/-- Equality at deterministic points of a subset extends simultaneously
to its closure for continuous versions. This includes both time endpoints. -/
theorem ae_eq_closure {Ω T E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace T] [SecondCountableTopology T] [TopologicalSpace E] [T2Space E]
    (μ : Measure Ω) (f g : T → Ω → E)
    (hf : ∀ ω, Continuous (fun t => f t ω)) (hg : ∀ ω, Continuous (fun t => g t ω))
    (S : Set T) (he : ∀ t ∈ S, f t =ᵐ[μ] g t) :
    ∀ᵐ ω ∂μ, ∀ t ∈ closure S, f t ω = g t ω := by
  have hh := NativeVectorProjection.continuous_versions μ
    (fun (t : S) ω => f t ω) (fun (t : S) ω => g t ω)
    (Filter.Eventually.of_forall fun ω => (hf ω).comp continuous_subtype_val)
    (Filter.Eventually.of_forall fun ω => (hg ω).comp continuous_subtype_val)
    (fun t => he t t.property)
  filter_upwards [hh] with ω hω t ht
  have hs : S ⊆ {s | f s ω = g s ω} := fun s hs => hω ⟨s,hs⟩
  exact (isClosed_eq (hf ω) (hg ω)).closure_subset_iff.mpr hs ht

end SHEStochastic.AEContinuousClosedSet
