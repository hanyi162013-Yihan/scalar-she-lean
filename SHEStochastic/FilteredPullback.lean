module

public import SHEStochastic.FiniteScalarIto
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FilteredPullback
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω Ξ E : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  {F : Filtration ℝ≥0 mΩ} {G : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
  (π : Ξ → Ω)

def timeMap (p : ℝ≥0 × Ξ) : ℝ≥0 × Ω := (p.1, π p.2)

theorem predictable_map (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π) :
    @Measurable (ℝ≥0 × Ξ) (ℝ≥0 × Ω) G.predictable F.predictable (timeMap π) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[G.predictable] ({⊥} ×ˢ (π ⁻¹' A))
    exact measurableSet_predictable_singleton_bot_prod (hfil ⊥ hA)
  · intro t A hA
    change MeasurableSet[G.predictable] (Set.Ioi t ×ˢ (π ⁻¹' A))
    exact measurableSet_predictable_Ioi_prod (hfil t hA)

theorem input_preserving (hπ : MeasurePreserving π ν μ)
    (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π) :
    @MeasurePreserving (ℝ≥0 × Ξ) (ℝ≥0 × Ω) G.predictable F.predictable (timeMap π)
      (FiniteScalarIto.inputMeasure G ν H) (FiniteScalarIto.inputMeasure F μ H) := by
  have hm := predictable_map π hfil
  have hp := (MeasurePreserving.id (MathFin.ItoIntegralCLM.timeMeasure_T H)).prod hπ
  have hpre (A : Set (ℝ≥0 × Ω)) (hA : MeasurableSet[F.predictable] A) :
      ((MathFin.ItoIntegralCLM.timeMeasure_T H).prod ν) ((timeMap π) ⁻¹' A) =
        ((MathFin.ItoIntegralCLM.timeMeasure_T H).prod μ) A :=
    hp.measure_preimage (F.predictable_le_prod A hA).nullMeasurableSet
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA]
  change (((MathFin.ItoIntegralCLM.timeMeasure_T H).prod ν).trim G.predictable_le_prod)
      ((timeMap π) ⁻¹' A) =
    (((MathFin.ItoIntegralCLM.timeMeasure_T H).prod μ).trim F.predictable_le_prod) A
  rw [trim_measurableSet_eq G.predictable_le_prod (hm hA),
    trim_measurableSet_eq F.predictable_le_prod hA]
  exact hpre A hA

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

def input (hπ : MeasurePreserving π ν μ) (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π) :
    Lp E 2 (FiniteScalarIto.inputMeasure F μ H) →ₗᵢ[ℝ]
      Lp E 2 (FiniteScalarIto.inputMeasure G ν H) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  exact Lp.compMeasurePreservingₗᵢ ℝ (timeMap π) (input_preserving π hπ hfil)

def output (hπ : MeasurePreserving π ν μ) : Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 ν :=
  Lp.compMeasurePreservingₗᵢ ℝ π hπ

theorem input_ae (hπ : MeasurePreserving π ν μ) (hfil : ∀ t, @Measurable Ξ Ω (G t) (F t) π)
    (f : Lp E 2 (FiniteScalarIto.inputMeasure F μ H)) :
    input π hπ hfil f =ᵐ[FiniteScalarIto.inputMeasure G ν H] fun p ↦ f (timeMap π p) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  letI : MeasurableSpace (ℝ≥0 × Ξ) := G.predictable
  exact Lp.coeFn_compMeasurePreserving _ _

theorem output_ae (hπ : MeasurePreserving π ν μ) (f : Lp E 2 μ) :
    output π hπ f =ᵐ[ν] fun ξ ↦ f (π ξ) := Lp.coeFn_compMeasurePreserving _ _

end SHEStochastic.FilteredPullback
