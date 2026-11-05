module

public import SHE.PastParameterExpectation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PastParameterConditional
open Set MeasureTheory Filter Topology
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (m : MeasurableSpace Ω) (hm : m≤mΩ) (μ : @Measure Ω mΩ)

include hm in
/-- Conditional simple-parameter approximation preserves the exact
past-event identities. The parameter and the event use the SAME past
sigma algebra, and all integrals use the original probability measure. -/
theorem integral_random_on_event_eq_zero (K : X→Ω→ℝ)
    (hK : @Measurable (X×Ω) ℝ ((inferInstance : MeasurableSpace X).prod mΩ) inferInstance (fun p => K p.1 p.2))
    (b : Ω→ℝ) (hb : Integrable b μ) (hbound : ∀ x ω,‖K x ω‖≤b ω)
    (hzero : ∀ x A,MeasurableSet[m] A → (∫ ω in A,K x ω ∂μ)=0)
    {u : Ω→X} (hu : StronglyMeasurable[m] u) (hc : ∀ ω,Continuous (fun x => K x ω))
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    Integrable (fun ω => K (u ω) ω) (μ.restrict A) ∧ (∫ ω in A,K (u ω) ω ∂μ)=0 := by
  have hz : ∀ x B,MeasurableSet[m] B → (∫ ω in B,K x ω ∂μ.restrict A)=0 := by
    intro x B hB
    rw [Measure.restrict_restrict (hm _ hB)]
    exact hzero x (B∩A) (hB.inter hA)
  exact PastParameterExpectation.integral_random_eq_zero (mΩ := mΩ) m hm (μ.restrict A) K hK b
    hb.restrict hbound hz hu hc

end SHE.PastParameterConditional
