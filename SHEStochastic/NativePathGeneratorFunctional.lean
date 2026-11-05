module

public import SHEStochastic.PastedGeneratorFunctional
public import SHE.NativeContinuousPath
public import SHEStochastic.AdaptedCanonicalPathTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativePathGeneratorFunctional
open MeasureTheory SHE StoppedPathPasting Set
open scoped NNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  (H : ℝ≥0) (W : ℝ≥0 → Ω → E) (hcW : ∀ sample, Continuous (fun t ↦ W t sample))

/-- The compact native path's constant extension agrees with the
original state throughout its actual time interval. -/
theorem read_eq (sample : Ω) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) H) :
    PastedGeneratorFunctional.read H (NativeContinuousPath.path H W hcW sample) r = W r.toNNReal sample :=
  PastedGeneratorFunctional.read_val H (NativeContinuousPath.path H W hcW sample) ⟨r, hr⟩

/-- Literal identification of the reusable path-law generator
functional with the original native state and its real time integral. -/
theorem value_eq (f b : E → ℝ) (sample : Ω) (t : Time H) :
    PastedGeneratorFunctional.value H f b (NativeContinuousPath.path H W hcW sample) t =
      f (W t.val.toNNReal sample) - f (W 0 sample) -
        ∫ r in (0 : ℝ)..t.val, b (W r.toNNReal sample) := by
  have hi : (∫ r in (0 : ℝ)..t.val,
      b (PastedGeneratorFunctional.read H (NativeContinuousPath.path H W hcW sample) r)) =
      ∫ r in (0 : ℝ)..t.val, b (W r.toNNReal sample) := by
    apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
    intro r hr
    exact congrArg b (read_eq H W hcW sample r ⟨hr.1.le, hr.2.le.trans t.property.2⟩)
  unfold PastedGeneratorFunctional.value
  rw [hi]
  change f (W t.val.toNNReal sample) - f (W (0 : ℝ).toNNReal sample) - _ = _
  rw [Real.toNNReal_zero]

theorem value_eq_toNN (f b : E → ℝ) (sample : Ω) (t : Time H) :
    PastedGeneratorFunctional.value H f b (NativeContinuousPath.path H W hcW sample) t =
      f (W (AdaptedCanonicalPathTests.toNN H t) sample) - f (W 0 sample) -
        ∫ r in (0 : ℝ)..(AdaptedCanonicalPathTests.toNN H t : ℝ), b (W r.toNNReal sample) := by
  have ht : t.val.toNNReal = AdaptedCanonicalPathTests.toNN H t :=
    NNReal.eq (Real.coe_toNNReal t.val t.property.1)
  convert value_eq H W hcW f b sample t using 1 <;> rw [ht] <;> rfl

theorem martingale_eq_capped (f b : E → ℝ) (sample : Ω) (q : ℝ≥0) :
    AdaptedCanonicalPathTests.martingale H (NativeContinuousPath.path H W hcW) f b q sample =
      f (W (min q H) sample) - f (W 0 sample) -
        ∫ r in (0 : ℝ)..(min q H : ℝ≥0), b (W r.toNNReal sample) := by
  rw [AdaptedCanonicalPathTests.martingale, value_eq_toNN, AdaptedCanonicalPathTests.toNN_clock]

theorem adapted [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
    (t : Time H) : Measurable[F (AdaptedCanonicalPathTests.toNN H t)]
      (fun sample ↦ NativeContinuousPath.path H W hcW sample t) := by
  have ht : t.val.toNNReal = AdaptedCanonicalPathTests.toNN H t :=
    NNReal.eq (Real.coe_toNNReal t.val t.property.1)
  change Measurable[F (AdaptedCanonicalPathTests.toNN H t)] (fun sample ↦ W t.val.toNNReal sample)
  rw [ht]
  exact ((show IsStronglyPredictable F W from hW).stronglyAdapted _).measurable

end SHEStochastic.NativePathGeneratorFunctional
