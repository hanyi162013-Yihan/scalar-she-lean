module

public import SHE.NativeContinuousPath
public import SHE.CouplingLaws
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativePathCoupling
open MeasureTheory Set
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (U V : ℝ≥0 → Ω → E)
variable (hc : ∀ ω, Continuous (fun t => U t ω))
variable (hd : ∀ ω, Continuous (fun t => V t ω))
local instance integratedMeasurable : MeasurableSpace (Lp E 2 (SHE.timeMeasure (H : ℝ))) := borel _
local instance integratedBorel : BorelSpace (Lp E 2 (SHE.timeMeasure (H : ℝ))) := ⟨rfl⟩
local instance twoFinite : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

def joint : ProbabilityMeasure
    (Lp E 2 (SHE.timeMeasure (H : ℝ)) × Lp E 2 (SHE.timeMeasure (H : ℝ))) :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
    (fun ω => (NativeContinuousPath.integrated H U hc ω,
      NativeContinuousPath.integrated H V hd ω))

variable (hU : Measurable (Function.uncurry U)) (hV : Measurable (Function.uncurry V))
include hU hV

theorem first_marginal :
    ProbabilityMeasure.map (joint μ H U V hc hd) Prod.fst =
      ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
        (NativeContinuousPath.integrated H U hc) := by
  apply Subtype.ext
  change Measure.map Prod.fst (μ.map _) = _
  rw [Measure.map_map measurable_fst
    ((NativeContinuousPath.measurable_integrated H U hc hU).prodMk
      (NativeContinuousPath.measurable_integrated H V hd hV))]
  rfl

theorem second_marginal :
    ProbabilityMeasure.map (joint μ H U V hc hd) Prod.snd =
      ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
        (NativeContinuousPath.integrated H V hd) := by
  apply Subtype.ext
  change Measure.map Prod.snd (μ.map _) = _
  rw [Measure.map_map measurable_snd
    ((NativeContinuousPath.measurable_integrated H U hc hU).prodMk
      (NativeContinuousPath.measurable_integrated H V hd hV))]
  rfl

variable (hi : Integrable (fun z : ℝ≥0 × Ω => ‖U z.1 z.2 - V z.1 z.2‖ ^ 2)
  (PredictableL2.energyMeasure μ H))
include hi

/-- The actual joint path law has exactly the native global difference energy.
Neither a deterministic surrogate nor an assumed quantitative coupling is used. -/
theorem energy_identity :
    couplingEnergy (joint μ H U V hc hd) =
      ∫ z : ℝ≥0 × Ω, ‖U z.1 z.2 - V z.1 z.2‖ ^ 2
        ∂PredictableL2.energyMeasure μ H := by
  change (∫ z : Lp E 2 (SHE.timeMeasure (H : ℝ)) ×
    Lp E 2 (SHE.timeMeasure (H : ℝ)), ‖z.1-z.2‖^2 ∂μ.map
      (fun ω => (NativeContinuousPath.integrated H U hc ω,
        NativeContinuousPath.integrated H V hd ω))) = _
  have hmap : (∫ z : Lp E 2 (SHE.timeMeasure (H : ℝ)) ×
      Lp E 2 (SHE.timeMeasure (H : ℝ)), ‖z.1-z.2‖^2 ∂μ.map
        (fun ω => (NativeContinuousPath.integrated H U hc ω,
          NativeContinuousPath.integrated H V hd ω))) =
      ∫ ω, ‖NativeContinuousPath.integrated H U hc ω -
        NativeContinuousPath.integrated H V hd ω‖^2 ∂μ := by
    exact integral_map
      (((NativeContinuousPath.measurable_integrated H U hc hU).prodMk
        (NativeContinuousPath.measurable_integrated H V hd hV)).aemeasurable)
      (show Continuous (fun z : Lp E 2 (SHE.timeMeasure (H : ℝ)) ×
        Lp E 2 (SHE.timeMeasure (H : ℝ)) => ‖z.1-z.2‖^2) from by fun_prop).aestronglyMeasurable
  rw [hmap]
  simp_rw [NativeContinuousPath.difference_norm_sq]
  exact (integral_prod_symm _ hi).symm

/-- Finiteness of the actual native energy supplies the genuine L2 moment of
the joint-law difference, as required by the bounded-Lipschitz coupling theorem. -/
theorem moment :
    MemLp (fun z : Lp E 2 (SHE.timeMeasure (H : ℝ)) ×
      Lp E 2 (SHE.timeMeasure (H : ℝ)) => z.1 - z.2) 2
      (joint μ H U V hc hd : Measure _) := by
  have hj := (NativeContinuousPath.measurable_integrated H U hc hU).prodMk
    (NativeContinuousPath.measurable_integrated H V hd hV)
  change MemLp (fun z : Lp E 2 (SHE.timeMeasure (H : ℝ)) ×
    Lp E 2 (SHE.timeMeasure (H : ℝ)) => z.1 - z.2) 2 (μ.map _)
  apply (memLp_map_measure_iff
    (continuous_fst.sub continuous_snd).aestronglyMeasurable hj.aemeasurable).mpr
  apply (memLp_two_iff_integrable_sq_norm
    ((NativeContinuousPath.measurable_integrated H U hc hU).sub
      (NativeContinuousPath.measurable_integrated H V hd hV)).aestronglyMeasurable).mpr
  simpa only [Function.comp_def, Pi.sub_apply, NativeContinuousPath.difference_norm_sq] using
    hi.integral_prod_right

end SHE.NativePathCoupling
