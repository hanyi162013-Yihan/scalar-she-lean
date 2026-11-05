module

public import SHEStochastic.BorelContinuationLawRecovery

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.ProjectedContinuationRecovery
open MeasureTheory ProbabilityTheory StoppedPathPasting
open scoped NNReal

variable {Ω E D : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [AddCommGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D] [T2Space D]
  [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
  (H : ℝ≥0)

/-- Retain only the state path, without imposing a norm on the driver. -/
def project (x : Path H (E × D)) : Path H E :=
  ⟨fun t ↦ (x t).1, continuous_fst.comp x.continuous⟩

theorem measurable_project : Measurable (project (E := E) (D := D) H) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact measurable_fst.comp (ContinuousMap.measurable_eval t)

theorem project_paste (r : Time H) (x y : Path H (E × D)) :
    project H (paste H r x y) = paste H r (project H x) (project H y) := by
  ext t
  rfl

variable (a : E → ℝ) (ha : Measurable a) (R : ℝ)
  (X : Ω → Path H (E × D)) (hX : Measurable X)

def cut (sample : Ω) : Time H := BorelObservablePath.exit H a R (project H (X sample))

include ha hX in
theorem measurable_cut : Measurable (cut H a R X) :=
  (BorelObservablePath.measurable_exit H a ha R).comp ((measurable_project H).comp hX)

variable (μ : Measure Ω) [SFinite μ]
  (κ : Kernel (E × D) (Path H (E × D))) [IsMarkovKernel κ]

/-- Joint pasting preserves the initial STATE even when the joining
driver is countable and only carries its product topology. -/
theorem initial (u : E)
    (hi : ∀ᵐ sample ∂μ, project H (X sample) (origin H) = u) :
    ∀ᵐ x ∂StoppedContinuationMeasure.law H X (cut H a R X) hX (measurable_cut H a ha R X hX) μ κ,
      project H x (origin H) = u := by
  let r := cut H a R X
  have hr := measurable_cut H a ha R X hX
  let ν := StoppedContinuationMeasure.joint H X r hX hr μ κ
  have hf : MeasurePreserving Prod.fst ν μ := ⟨measurable_fst, Measure.fst_compProd μ _⟩
  apply (ae_map_iff (StoppedContinuationMeasure.measurable_value H X r hX hr).aemeasurable
    (measurableSet_eq_fun ((ContinuousMap.measurable_eval (origin H)).comp (measurable_project H)) measurable_const)).mpr
  filter_upwards [hf.quasiMeasurePreserving.ae hi] with z hz
  change project H (paste H (r z.1) (X z.1) z.2) (origin H) = u
  rw [project_paste, paste_before H _ _ _ _ (r z.1).property.1]
  exact hz

/-- Recover the original stopped state law from its actual JOINT
continuation law. The driver space need not be normable, and the
continuation kernel may differ between the two compared solutions. -/
theorem stopped_law
    (hc : ∀ᵐ sample ∂μ, Continuous (fun t ↦ a (project H (X sample) t)))
    (hp : ∀ᵐ x ∂StoppedContinuationMeasure.law H X (cut H a R X) hX
      (measurable_cut H a ha R X hX) μ κ, Continuous (fun t ↦ a (project H x t))) :
    ((StoppedContinuationMeasure.law H X (cut H a R X) hX (measurable_cut H a ha R X hX) μ κ).map
      (project H)).map (BorelObservablePath.stopped H a R) =
        μ.map (fun sample ↦ BorelObservablePath.stopped H a R (project H (X sample))) := by
  let r := cut H a R X
  have hr := measurable_cut H a ha R X hX
  let ν := StoppedContinuationMeasure.joint H X r hX hr μ κ
  have hf : MeasurePreserving Prod.fst ν μ := ⟨measurable_fst, Measure.fst_compProd μ _⟩
  have hpa := ae_of_ae_map (StoppedContinuationMeasure.measurable_value H X r hX hr).aemeasurable hp
  have he : (fun z : Ω × Path H (E × D) ↦ BorelObservablePath.stopped H a R
      (project H (StoppedContinuationMeasure.value H X r z))) =ᵐ[ν]
        fun z ↦ BorelObservablePath.stopped H a R (project H (X z.1)) := by
    filter_upwards [hf.quasiMeasurePreserving.ae hc, hpa] with z hc hp
    have hh := BorelObservablePath.stopped_paste H a R (project H (X z.1)) (project H z.2) hc
      (by simpa only [StoppedContinuationMeasure.value, project_paste, r, cut] using hp)
    simpa only [StoppedContinuationMeasure.value, project_paste, r, cut] using hh
  rw [Measure.map_map (BorelObservablePath.measurable_stopped H a ha R) (measurable_project H)]
  change (ν.map (StoppedContinuationMeasure.value H X r)).map _ = _
  rw [Measure.map_map ((BorelObservablePath.measurable_stopped H a ha R).comp (measurable_project H))
    (StoppedContinuationMeasure.measurable_value H X r hX hr)]
  calc
    _ = ν.map (fun z ↦ BorelObservablePath.stopped H a R (project H (X z.1))) := Measure.map_congr he
    _ = (ν.map Prod.fst).map (fun sample ↦ BorelObservablePath.stopped H a R (project H (X sample))) :=
      (Measure.map_map ((BorelObservablePath.measurable_stopped H a ha R).comp
        ((measurable_project H).comp hX)) measurable_fst).symm
    _ = _ := by rw [hf.map_eq]

end SHEStochastic.ProjectedContinuationRecovery
