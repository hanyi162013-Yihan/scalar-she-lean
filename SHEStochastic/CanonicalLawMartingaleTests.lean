module

public import SHEStochastic.ContinuousStoppedMartingaleTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.CanonicalLawMartingaleTests
open MeasureTheory
open scoped NNReal

/-- Transfer any original martingale's closed-horizon representation
to full-past tests of its actual path law. This also covers square and
mixed compensators without repeating the law-transport proof. -/
theorem identity {Ω X Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0)
    (Z : Ω → X) (hZ : Measurable Z) (past : ℝ≥0 → X → Y)
    (hpast : ∀ s, Continuous (past s))
    (hPast : ∀ s, Measurable[F (min s H)] ((past s) ∘ Z))
    (A : ℝ≥0 → X → ℝ) (hA : ∀ t, Continuous (A t))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ)
    (hRep : ∀ t, (A t ∘ Z) =ᵐ[μ] M (min t H))
    (s t : ℝ≥0) (hst : s ≤ t) (ψ : BoundedContinuousFunction Y ℝ) :
    (∫ x, ψ (past s x)*(A t x-A s x) ∂μ.map Z) = 0 := by
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F M hM
    (min s H) (min t H) (min_le_min_right _ hst)
    (fun sample ↦ ψ (past s (Z sample)))
    (ψ.continuous.measurable.comp (hPast s)).stronglyMeasurable ‖ψ‖
    (fun sample ↦ ψ.norm_coe_le_norm _)
  have hψ : AEStronglyMeasurable (fun x ↦ ψ (past s x)*(A t x-A s x)) (μ.map Z) :=
    ((ψ.continuous.comp (hpast s)).mul ((hA t).sub (hA s))).stronglyMeasurable.aestronglyMeasurable
  rw [integral_map hZ.aemeasurable hψ]
  calc
    _ = ∫ sample, ψ (past s (Z sample))*(M (min t H) sample-M (min s H) sample) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hRep t, hRep s] with sample ht hs
      dsimp only [Function.comp_apply] at ht hs
      rw [ht, hs]
    _ = 0 := hh

end SHEStochastic.CanonicalLawMartingaleTests
