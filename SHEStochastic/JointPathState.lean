module

public import SHEStochastic.JointPathFiltration
public import SHEStochastic.PastedHeatCovariance
public import SHE.ContinuousPredictable
public import SHE.NativeContinuousPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.JointPathState
open MeasureTheory SHE StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι] (H : ℝ≥0)

def state (q : ℝ≥0) (x : JointPathFiltration.Space (E := E) (ι := ι) H) : E := (x (clock H q)).1

theorem adapted (q : ℝ≥0) : Measurable[JointPathFiltration.filtration H q] (state (E := E) (ι := ι) H q) :=
  ((JointPathFiltration.evaluation_adapted H (clock H q)).mono
    ((JointPathFiltration.filtration H).mono (show toNN H (clock H q) ≤ q from min_le_left _ _)) le_rfl).fst

theorem continuous (x : JointPathFiltration.Space (E := E) (ι := ι) H) : Continuous (fun q ↦ state H q x) :=
  continuous_fst.comp (x.continuous.comp (continuous_clock H))

theorem predictable : StronglyMeasurable[(JointPathFiltration.filtration H).predictable]
    (Function.uncurry (state (E := E) (ι := ι) H)) :=
  ContinuousPredictable.stronglyMeasurable (JointPathFiltration.filtration H) (state H)
    (fun q ↦ (adapted H q).stronglyMeasurable) (continuous H)

theorem initial (x : JointPathFiltration.Space (E := E) (ι := ι) H) : state H 0 x = (x (origin H)).1 := by
  have hz : clock H 0 = origin H := Subtype.ext (min_eq_left H.property)
  simp only [state, hz]

theorem at_time (t : Time H) (x : JointPathFiltration.Space (E := E) (ι := ι) H) :
    state H (toNN H t) x = (x t).1 := by simp only [state, clock_toNN]

/-- Reading the clipped canonical state reconstructs precisely the
state projection of the original joint path. -/
theorem path (x : JointPathFiltration.Space (E := E) (ι := ι) H) :
    NativeContinuousPath.path H (state H) (continuous H) x =
      (⟨fun t ↦ (x t).1, continuous_fst.comp x.continuous⟩ : Path H E) := by
  ext t
  change state H t.val.toNNReal x = (x t).1
  have ht : t.val.toNNReal = toNN H t := NNReal.eq (Real.coe_toNNReal _ t.property.1)
  rw [ht, at_time]

theorem read (x : JointPathFiltration.Space (E := E) (ι := ι) H) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) H) :
    (PastedGeneratorFunctional.read H x s).1 = state H s.toNNReal x := by
  have ht : (⟨s, hs⟩ : Time H).val.toNNReal = toNN H ⟨s, hs⟩ :=
    NNReal.eq (Real.coe_toNNReal _ hs.1)
  rw [show PastedGeneratorFunctional.read H x s = x ⟨s, hs⟩ from
    PastedGeneratorFunctional.read_val H x ⟨s, hs⟩, ht, at_time]

theorem covariance (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction E ℝ)
    (q : ℝ≥0) (x : JointPathFiltration.Space (E := E) (ι := ι) H) :
    PastedHeatCovariance.value H rate hrate (b.compContinuous ⟨Prod.fst, continuous_fst⟩) x (clock H q) =
      ∫ s in (0 : ℝ)..(min q H : ℝ≥0), Real.exp (s*rate)*b (state H s.toNNReal x) := by
  rw [PastedHeatCovariance.value_eq]
  apply intervalIntegral.integral_congr_Ioo_of_le (clock H q).property.1
  intro s hs
  dsimp only
  change Real.exp (rate*s)*b ((PastedGeneratorFunctional.read H x s).1) = _
  rw [read H x s ⟨hs.1.le, hs.2.le.trans (clock H q).property.2⟩, mul_comm rate s]

end SHEStochastic.JointPathState
