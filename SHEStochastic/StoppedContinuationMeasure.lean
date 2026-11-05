module

public import SHEStochastic.StoppedPathPasting
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.StoppedContinuationMeasure
open MeasureTheory ProbabilityTheory StoppedPathPasting
open scoped NNReal ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (H : ℝ≥0)
  (X : Ω → Path H E) (r : Ω → Time H) (hX : Measurable X) (hr : Measurable r)

def state (ω : Ω) : E := X ω (r ω)

include hX hr in
theorem measurable_state : Measurable (state H X r) :=
  continuous_eval.measurable.comp (hX.prodMk hr)

def continuation (κ : Kernel E (Path H E)) : Kernel Ω (Path H E) :=
  κ.comap (state H X r) (measurable_state H X r hX hr)

instance continuation_markov (κ : Kernel E (Path H E)) [IsMarkovKernel κ] :
    IsMarkovKernel (continuation H X r hX hr κ) := inferInstanceAs (IsMarkovKernel (κ.comap _ _))

/-- Keep the original sample, then sample a continuation from its
actual state at the random join. Existence of this Borel solution kernel
remains a separate SPDE theorem, not an assumed uniqueness conclusion. -/
def joint (μ : Measure Ω) (κ : Kernel E (Path H E)) : Measure (Ω × Path H E) :=
  μ ⊗ₘ continuation H X r hX hr κ

instance joint_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (joint H X r hX hr μ κ) :=
  inferInstanceAs (IsProbabilityMeasure (μ ⊗ₘ continuation H X r hX hr κ))

def value (z : Ω × Path H E) : Path H E := paste H (r z.1) (X z.1) z.2

include hX hr in
theorem measurable_value : Measurable (value H X r) :=
  (continuous_paste H).measurable.comp ((hr.comp measurable_fst).prodMk
    ((hX.comp measurable_fst).prodMk measurable_snd))

def law (μ : Measure Ω) (κ : Kernel E (Path H E)) : Measure (Path H E) :=
  (joint H X r hX hr μ κ).map (value H X r)

theorem law_congr_exit (s : Ω → Time H) (hs : Measurable s) (he : r = s)
    (μ : Measure Ω) (κ : Kernel E (Path H E)) :
    law H X r hX hr μ κ = law H X s hX hs μ κ := by
  subst s
  rfl

instance law_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (law H X r hX hr μ κ) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_value H X r hX hr).aemeasurable).mpr inferInstance

theorem matching_initial_of_ae (μ : Measure Ω) (κ : Kernel E (Path H E))
    (hκ : ∀ᵐ sample ∂μ, ∀ᵐ y ∂κ (state H X r sample),
      y (origin H) = state H X r sample) :
    ∀ᵐ z ∂joint H X r hX hr μ κ, z.2 (origin H) = X z.1 (r z.1) := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((ContinuousMap.measurable_eval (origin H)).comp measurable_snd)
      ((measurable_state H X r hX hr).comp measurable_fst))
  exact hκ

theorem matching_initial (μ : Measure Ω) (κ : Kernel E (Path H E))
    (hκ : ∀ z : E, ∀ᵐ y ∂κ z, y (origin H) = z) :
    ∀ᵐ z ∂joint H X r hX hr μ κ, z.2 (origin H) = X z.1 (r z.1) :=
  matching_initial_of_ae H X r hX hr μ κ
    (Filter.Eventually.of_forall fun sample ↦ hκ (state H X r sample))

theorem future_unshifted (μ : Measure Ω) (κ : Kernel E (Path H E))
    (hκ : ∀ z : E, ∀ᵐ y ∂κ z, y (origin H) = z) :
    ∀ᵐ z ∂joint H X r hX hr μ κ, ∀ t : Time H, (r z.1).val ≤ t.val →
      value H X r z t = z.2 (futureTime H (r z.1) t) := by
  exact (matching_initial H X r hX hr μ κ hκ).mono fun z hz t ht ↦
    paste_after H (r z.1) t (X z.1) z.2 ht hz

/-- Pasting preserves the stopped path pointwise, including the join. -/
theorem stopped_value (z : Ω × Path H E) :
    stopped H (r z.1) (value H X r z) = stopped H (r z.1) (X z.1) :=
  stopped_paste H (r z.1) (X z.1) z.2

/-- The stopped-prefix distribution of the constructed enlargement is
exactly the original one. This is proved for the actual kernel product. -/
theorem stopped_prefix_law (μ : Measure Ω) [SFinite μ]
    (κ : Kernel E (Path H E)) [IsMarkovKernel κ] :
    (joint H X r hX hr μ κ).map (fun z ↦ stopped H (r z.1) (value H X r z)) =
      μ.map (fun ω ↦ stopped H (r ω) (X ω)) := by
  have hm : Measurable (fun ω ↦ stopped H (r ω) (X ω)) :=
    (continuous_stopped H).measurable.comp (hr.prodMk hX)
  calc
    _ = (joint H X r hX hr μ κ).map (fun z ↦ stopped H (r z.1) (X z.1)) := by
      congr 1
      funext z
      exact stopped_value H X r z
    _ = ((joint H X r hX hr μ κ).map Prod.fst).map (fun ω ↦ stopped H (r ω) (X ω)) :=
      (Measure.map_map hm measurable_fst).symm
    _ = _ := by change ((μ ⊗ₘ continuation H X r hX hr κ).fst).map _ = _; rw [Measure.fst_compProd]

end SHEStochastic.StoppedContinuationMeasure
