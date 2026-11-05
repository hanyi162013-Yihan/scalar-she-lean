module

public import SHEStochastic.CanonicalCylinderRecognition
public import SHEStochastic.WeakLimitCanonicalBrownian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.JointCanonicalCylinderRecognition
open MeasureTheory SHE StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι] (H : ℝ≥0)

abbrev Space := CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H

theorem history_generates (s : ℝ≥0) :
    CanonicalStateDriverFiltration.filtration (E := E) (ι := ι) H s ≤
      MeasurableSpace.comap
        (fun x : Space (E := E) (ι := ι) H ↦
          CanonicalCylinderRecognition.history H s (JointStateDriverPath.pack H x)) inferInstance := by
  change MeasurableSpace.comap (CanonicalStateDriverFiltration.history H s) _ ≤ _
  have he : CanonicalStateDriverFiltration.history (E := E) (ι := ι) H s =
      JointStateDriverPath.unpack H ∘
        (fun x ↦ CanonicalCylinderRecognition.history H s (JointStateDriverPath.pack H x)) := by
    funext x
    rfl
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (JointStateDriverPath.measurable_unpack H).comap_le

theorem adapted (t : Time H) :
    Measurable[CanonicalStateDriverFiltration.filtration (E := E) (ι := ι) H (toNN H t)]
      (fun x : Space (E := E) (ι := ι) H ↦ JointStateDriverPath.pack H x t) := by
  have hm := ((ContinuousMap.measurable_eval t).comp (JointStateDriverPath.measurable_pack H)).comp
    (Measurable.of_comap_le
      (f := CanonicalStateDriverFiltration.history (E := E) (ι := ι) H (toNN H t)) le_rfl)
  have he : (fun x : Space (E := E) (ι := ι) H ↦
      JointStateDriverPath.pack H (CanonicalStateDriverFiltration.history H (toNN H t) x) t) =
      fun x ↦ JointStateDriverPath.pack H x t := by
    funext x
    change JointStateDriverPath.pack H x (pastTime H (clock H (toNN H t)) t) = _
    rw [clock_toNN]
    congr 1
    exact Subtype.ext (min_self _)
  exact he ▸ hm

/-- Joint compact cylinder identities on the limiting law give actual
martingales in the existing state-and-driver filtration. The path
presentation used for pasting and the Brownian presentation use the
same measurable histories. -/
theorem martingale (μ : Measure (Space (E := E) (ι := ι) H)) [IsProbabilityMeasure μ]
    (f b : BoundedContinuousFunction (E × (ι → ℝ)) ℝ)
    (h : PastedCylinderMartingale.Identity H f b (μ.map (JointStateDriverPath.pack H))) :
    Martingale (AdaptedCanonicalPathTests.martingale H (JointStateDriverPath.pack H) f b)
      (CanonicalStateDriverFiltration.filtration H) μ :=
  CanonicalCylinderRecognition.along_path H μ (CanonicalStateDriverFiltration.filtration H)
    (JointStateDriverPath.pack H) (JointStateDriverPath.measurable_pack H)
    (adapted H) (history_generates H) f b h

end SHEStochastic.JointCanonicalCylinderRecognition
