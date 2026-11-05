module

public import SHE.PastParameterDiagonal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PastParameterHistoryExpectation
open Set MeasureTheory Filter Topology
variable {Ω X Γ : Type*} [mΩ : MeasurableSpace Ω] [mΓ : MeasurableSpace Γ]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (m : MeasurableSpace Ω) (hm : m≤mΩ)
variable (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] (ν : Measure Γ) [IsFiniteMeasure ν]

include hm in
/-- A finite history integral preserves the actual past-parameter
conditional cancellation. The diagonal is constructed by finite simple
past approximations, and its history/sample Fubini integrability is
proved from the uniform bound. No random-reference theorem is assumed. -/
theorem integral_random_on_event_eq_zero
    (K : X→Γ×Ω→ℝ) (hK : ∀ x,@Measurable (Γ×Ω) ℝ (mΓ.prod mΩ) inferInstance (K x))
    (hc : ∀ q : Γ×Ω,Continuous (fun x => K x q))
    {C : ℝ} (hb : ∀ x q,‖K x q‖≤C)
    (hz : ∀ x h A,@MeasurableSet Ω m A → (∫ ω in A,K x (h,ω) ∂μ)=0)
    {u : Ω→X} (hu : StronglyMeasurable[m] u)
    (A : Set Ω) (hA : @MeasurableSet Ω m A) :
    Integrable (fun q : Γ×Ω => K (u q.2) q) ((@Measure.prod Γ Ω mΓ mΩ ν (μ.restrict A))) ∧
      (∫ q : Γ×Ω,K (u q.2) q ∂(@Measure.prod Γ Ω mΓ mΩ ν (μ.restrict A)))=0 := by
  letI : MeasurableSpace Ω := mΩ
  have hmprod : mΓ.prod m≤mΓ.prod mΩ := sup_le_sup le_rfl (MeasurableSpace.comap_mono hm)
  have huprod : @StronglyMeasurable (Γ×Ω) X _ (mΓ.prod m) (fun q => u q.2) :=
    hu.comp_measurable measurable_snd
  have hdiag := PastParameterDiagonal.stronglyMeasurable_diagonal (mΓ.prod m) hmprod K hK huprod hc
  have hi : Integrable (fun q : Γ×Ω => K (u q.2) q) ((@Measure.prod Γ Ω mΓ mΩ ν (μ.restrict A))) :=
    (integrable_const C).mono' hdiag.aestronglyMeasurable (ae_of_all _ (fun q => hb (u q.2) q))
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  have hs (h : Γ) : (∫ ω in A,K (u ω) (h,ω) ∂μ)=0 := by
    have hsections (x : X) : Measurable (fun ω => K x (h,ω)) := by
      have hh := (hK x).comp ((measurable_const (a := h)).prodMk measurable_id)
      exact hh
    have hz' : ∀ x B,@MeasurableSet Ω m B → (∫ ω in B,K x (h,ω) ∂μ.restrict A)=0 := by
      intro x B hB
      rw [Measure.restrict_restrict (hm _ hB)]
      exact hz x h (B∩A) (hB.inter hA)
    exact (PastParameterSectionExpectation.integral_random_eq_zero (mΩ := mΩ) m hm (μ.restrict A)
      (fun x ω => K x (h,ω)) hsections (fun _ => C) (integrable_const C)
      (fun x ω => hb x (h,ω)) hz' hu (fun ω => hc (h,ω))).2
  simp only [hs,integral_zero]

end SHE.PastParameterHistoryExpectation
