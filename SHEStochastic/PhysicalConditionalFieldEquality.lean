module

public import SHEStochastic.PhysicalHeatParameterSection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PhysicalConditionalFieldEquality
open MeasureTheory SHE SHE.StoppedFourier AddCircle Filter Set
open HeatParameterCover HeatParameterPullback
open scoped ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Pointwise-in-space equalities before one localization event identify
actual spatial L2 sections on that event. Joint physical measurability
and ordinary Fubini handle the parameter-dependent exceptional sets. -/
theorem ae_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (Y Z : Parameter → Ω → ℝ) (hYm : ∀ p, Measurable (Y p))
    (hYc : ∀ ω, Continuous (fun p ↦ Y p ω)) (hZm : ∀ p, Measurable (Z p))
    (hZc : ∀ ω, Continuous (fun p ↦ Z p ω)) (t : ShortTime)
    (A : Set Ω) (hA : MeasurableSet A)
    (he : ∀ a : HeatCircle, ∀ᵐ ω ∂μ, ω ∈ A → Y (point t a) ω = Z (point t a) ω) :
    ∀ᵐ ω ∂μ, ω ∈ A →
      PhysicalHeatParameterSection.value 2 ⟨fun p ↦ Y p ω, hYc ω⟩ t =
        PhysicalHeatParameterSection.value 2 ⟨fun p ↦ Z p ω, hZc ω⟩ t := by
  have hm : Measurable (fun z : HeatCircle × Ω ↦ ((t, z.1), z.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hy := (measurable_physical Y hYm hYc).comp hm
  have hz := (measurable_physical Z hZm hZc).comp hm
  have hevent : MeasurableSet {z : HeatCircle × Ω | z.2 ∈ A → Y (point t z.1) z.2 = Z (point t z.1) z.2} := by
    convert (hA.preimage measurable_snd).compl.union (measurableSet_eq_fun hy hz) using 1
    ext z
    simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_preimage, physical, imp_iff_not_or]
    rfl
  have hp : ∀ᵐ z : HeatCircle × Ω ∂(haarAddCircle (T := 2 * Real.pi)).prod μ,
      z.2 ∈ A → Y (point t z.1) z.2 = Z (point t z.1) z.2 :=
    (Measure.ae_prod_iff_ae_ae hevent).mpr (Eventually.of_forall he)
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := (haarAddCircle (T := 2 * Real.pi)))).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω hωA
  apply Lp.ext
  filter_upwards [PhysicalHeatParameterSection.value_ae 2 ⟨fun p ↦ Y p ω, hYc ω⟩ t,
    PhysicalHeatParameterSection.value_ae 2 ⟨fun p ↦ Z p ω, hZc ω⟩ t, hω] with a hy hz heq
  rw [hy, hz]
  exact heq hωA

end SHEStochastic.PhysicalConditionalFieldEquality
