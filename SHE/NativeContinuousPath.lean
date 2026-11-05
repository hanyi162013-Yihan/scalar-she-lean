module

public import SHE.PathLaws
public import SHE.PredictableTime
public import SHE.ProcessEnergy
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeContinuousPath
open MeasureTheory Set
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
section Paths
variable [TopologicalSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (H : ℝ≥0) (U : ℝ≥0 → Ω → E)
variable (hc : ∀ ω, Continuous (fun t => U t ω))

/-- An actual native continuous trajectory, on the original compact time interval. -/
def path (ω : Ω) : C(Icc (0 : ℝ) (H : ℝ), E) :=
  ⟨fun t => U t.val.toNNReal ω,
    (hc ω).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩

@[simp] theorem path_apply (ω : Ω) (t : Icc (0 : ℝ) (H : ℝ)) :
    path H U hc ω t = U t.val.toNNReal ω := rfl

/-- Joint measurability of the given process supplies measurability of its
continuous-path random variable, without a new version or path-law assumption. -/
theorem measurable_path [RegularSpace E] (hm : Measurable (Function.uncurry U)) :
    Measurable (path H U hc) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact hm.comp (measurable_const.prodMk measurable_id)

end Paths

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (H : ℝ≥0) (U : ℝ≥0 → Ω → E)
variable (hc : ∀ ω, Continuous (fun t => U t ω))
local instance integratedMeasurable : MeasurableSpace (Lp E 2 (SHE.timeMeasure (H : ℝ))) := borel _
local instance integratedBorel : BorelSpace (Lp E 2 (SHE.timeMeasure (H : ℝ))) := ⟨rfl⟩

/-- The same genuine trajectory viewed in integrated Hilbert path space. -/
def integrated (ω : Ω) : Lp E 2 (SHE.timeMeasure (H : ℝ)) :=
  ContinuousMap.toLp 2 (SHE.timeMeasure (H : ℝ)) ℝ (path H U hc ω)

theorem measurable_integrated (hm : Measurable (Function.uncurry U)) :
    Measurable (integrated H U hc) :=
  (ContinuousMap.toLp (E := E) 2 (SHE.timeMeasure (H : ℝ)) ℝ).continuous.measurable.comp
    (measurable_path H U hc hm)

/-- Compact-interval and native predictable time integrals agree exactly.
The left endpoint contributes no artificial energy. -/
theorem time_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ≥0 → F) :
    (∫ t : Icc (0 : ℝ) (H : ℝ), f t.val.toNNReal ∂SHE.timeMeasure (H : ℝ)) =
      ∫ t, f t ∂PredictableL2.timeMeasure H := by
  rw [PredictableL2.timeMeasure_integral]
  change (∫ t : Icc (0 : ℝ) (H : ℝ), (fun r : ℝ => f r.toNNReal) t.val
      ∂volume.comap Subtype.val) = _
  exact (integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Icc (0 : ℝ) (H : ℝ)) measurableSet_Icc (fun r : ℝ => f r.toNNReal)).trans
      integral_Icc_eq_integral_Ioc

variable (V : ℝ≥0 → Ω → E) (hd : ∀ ω, Continuous (fun t => V t ω))

/-- The integrated trajectory difference has its literal native time energy,
for each sample, rather than a bound or a prescribed coupling cost. -/
theorem difference_norm_sq (ω : Ω) :
    ‖integrated H U hc ω - integrated H V hd ω‖ ^ 2 =
      ∫ t, ‖U t ω - V t ω‖ ^ 2 ∂PredictableL2.timeMeasure H := by
  have he : integrated H U hc ω - integrated H V hd ω =
      ContinuousMap.toLp 2 (SHE.timeMeasure (H : ℝ)) ℝ
        (path H U hc ω - path H V hd ω) := by
    simp only [integrated, map_sub]
  rw [he, PredictableL2.realLp_norm_sq]
  calc
    _ = ∫ t : Icc (0 : ℝ) (H : ℝ), ‖U t.val.toNNReal ω - V t.val.toNNReal ω‖ ^ 2
        ∂SHE.timeMeasure (H : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (SHE.timeMeasure (H : ℝ))
        (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (path H U hc ω - path H V hd ω)] with t ht
      rw [ht]
      rfl
    _ = _ := time_integral H (fun t => ‖U t ω - V t ω‖ ^ 2)

end SHE.NativeContinuousPath
