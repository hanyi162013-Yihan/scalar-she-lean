module

public import SHEStochastic.FamilyLpRepresentative
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.AdaptedLpRepresentative
open MeasureTheory
open scoped ENNReal

/-- A strongly measurable L2 family with adapted values has a representative
jointly measurable in the parameter and the actual past sigma algebra. -/
theorem exists_joint {X Ω : Type*} [MeasurableSpace X] [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (F : X → Lp ℝ 2 μ) (hF : StronglyMeasurable F)
    (ha : ∀ x, AEStronglyMeasurable[m] (F x : Ω → ℝ) μ) :
    ∃ Z : X × Ω → ℝ, @Measurable (X × Ω) ℝ
      ((inferInstance : MeasurableSpace X).prod m) _ Z ∧
      (∀ x, (fun ω ↦ Z (x, ω)) =ᵐ[μ] F x) := by
  letI : MeasurableSpace Ω := mΩ
  let G (x : X) : lpMeas ℝ ℝ m 2 μ := ⟨F x, mem_lpMeas_iff_aestronglyMeasurable.mpr (ha x)⟩
  have hG : StronglyMeasurable G :=
    (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).mp hF
  let L := lpMeasToLpTrimLie ℝ ℝ 2 μ hm
  have hLG : StronglyMeasurable (fun x ↦ L (G x)) :=
    L.continuous.comp_stronglyMeasurable hG
  let Z := @FamilyLpRepresentative.representative X Ω ℝ _ m _ _ _ _ _ (μ.trim hm) (fun x ↦ L (G x)) hLG
  refine ⟨Z, @FamilyLpRepresentative.representative_measurable X Ω ℝ _ m _ _ _ _ _
    (μ.trim hm) (fun x ↦ L (G x)) hLG, ?_⟩
  intro x
  exact (ae_eq_of_ae_eq_trim (@FamilyLpRepresentative.representative_ae X Ω ℝ _ m _ _ _ _ _
    (μ.trim hm) (fun x ↦ L (G x)) hLG x)).trans (lpMeasToLpTrim_ae_eq hm (G x))

end SHEStochastic.AdaptedLpRepresentative
