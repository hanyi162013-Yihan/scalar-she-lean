module

public import SHE.PastParameterSectionExpectation
public import SHE.PastParameterDiagonal
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.ParameterIntegralSections
open Set MeasureTheory Filter Topology
variable {P Γ Ω : Type*} [TopologicalSpace P] [FirstCountableTopology P]
variable [MeasurableSpace Γ] [MeasurableSpace Ω]
variable (ν : Measure Γ) [SFinite ν] (K : P→Γ×Ω→ℝ)
variable (hK : ∀ p,Measurable (K p)) (b : Γ→ℝ) (hb : Integrable b ν)
variable (hbound : ∀ p q,‖K p q‖≤b q.1)
variable (hc : ∀ q,Continuous (fun p => K p q))

def sectionValue (p : P) (ω : Ω) : ℝ := ∫ h,K p (h,ω) ∂ν

include hK in
theorem section_measurable (p : P) : Measurable (sectionValue ν K p) :=
  ((hK p).stronglyMeasurable.integral_prod_left' (μ:=ν)).measurable

include hK hb hbound hc in
theorem section_continuous (ω : Ω) : Continuous (fun p => sectionValue ν K p ω) := by
  apply continuous_of_dominated (bound:=b)
  · intro p
    exact ((hK p).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact fun p => Eventually.of_forall (fun h => hbound p (h,ω))
  · exact hb
  · exact Eventually.of_forall (fun h => hc (h,ω))

include hb hbound in
theorem section_bound (p : P) (ω : Ω) : ‖sectionValue ν K p ω‖≤∫ h,b h ∂ν :=
  norm_integral_le_of_norm_le hb (Eventually.of_forall (fun h => hbound p (h,ω)))

end SHE.ParameterIntegralSections

namespace SHE.PastParameterSectionConditional
open Set MeasureTheory Filter Topology
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (m : MeasurableSpace Ω) (hm : m≤mΩ) (μ : @Measure Ω mΩ)

include hm in
/-- Sectionwise measurable conditional parameter substitution. This
extends the actual finite-simple approximation proof to an integrated
finite tree without assuming a joint random-reference identity. -/
theorem integral_random_on_event_eq_zero (K : X→Ω→ℝ)
    (hK : ∀ x,@Measurable Ω ℝ mΩ inferInstance (K x))
    (b : Ω→ℝ) (hb : Integrable b μ) (hbound : ∀ x ω,‖K x ω‖≤b ω)
    (hzero : ∀ x A,MeasurableSet[m] A → (∫ ω in A,K x ω ∂μ)=0)
    {u : Ω→X} (hu : StronglyMeasurable[m] u) (hc : ∀ ω,Continuous (fun x => K x ω))
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    Integrable (fun ω => K (u ω) ω) (μ.restrict A) ∧ (∫ ω in A,K (u ω) ω ∂μ)=0 := by
  have hz : ∀ x B,MeasurableSet[m] B → (∫ ω in B,K x ω ∂μ.restrict A)=0 := by
    intro x B hB
    rw [Measure.restrict_restrict (hm _ hB)]
    exact hzero x (B∩A) (hB.inter hA)
  exact PastParameterSectionExpectation.integral_random_eq_zero (mΩ:=mΩ) m hm (μ.restrict A)
    K hK b hb.restrict hbound hz hu hc

end SHE.PastParameterSectionConditional
