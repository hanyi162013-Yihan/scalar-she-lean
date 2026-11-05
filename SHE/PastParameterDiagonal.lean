module

public import SHE.PastParameterSectionExpectation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.PastParameterDiagonal
open Set MeasureTheory Filter Topology
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (m : MeasurableSpace Ω) (hm : m≤mΩ)

include hm in
/-- A separately measurable, parameter-continuous random-reference
quantity has an actual strongly measurable past-parameter diagonal.
The proof uses finite simple approximations, including on arbitrary Ω. -/
theorem stronglyMeasurable_diagonal (K : X→Ω→ℝ)
    (hK : ∀ x,@Measurable Ω ℝ mΩ inferInstance (K x))
    {u : Ω→X} (hu : StronglyMeasurable[m] u) (hc : ∀ ω,Continuous (fun x => K x ω)) :
    @StronglyMeasurable Ω ℝ _ mΩ (fun ω => K (u ω) ω) := by
  have hm_n (n : ℕ) : @Measurable Ω ℝ mΩ inferInstance (fun ω => K ((hu.approx n) ω) ω) :=
    PastParameterSectionExpectation.simple_eval_measurable (mΩ := mΩ) m hm K hK (hu.approx n)
  apply stronglyMeasurable_of_tendsto atTop (fun n => (hm_n n).stronglyMeasurable)
  exact tendsto_pi_nhds.mpr (fun ω => ((hc ω).tendsto (u ω)).comp (hu.tendsto_approx ω))

end SHE.PastParameterDiagonal
