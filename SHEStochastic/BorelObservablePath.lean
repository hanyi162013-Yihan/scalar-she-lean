module

public import SHEStochastic.StoppedPathExitRecovery
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BorelObservablePath
open MeasureTheory StoppedPathPasting StoppedPathExitRecovery TopologicalSpace
open scoped NNReal

local instance (H : ℝ≥0) : Nonempty (Time H) := ⟨origin H⟩

def samples (H : ℝ≥0) (f : C(Time H, ℝ)) (n : ℕ) : ℝ := f (denseSeq (Time H) n)

theorem continuous_samples (H : ℝ≥0) : Continuous (samples H) :=
  continuous_pi fun n ↦ continuous_eval_const (denseSeq (Time H) n)

theorem samples_injective (H : ℝ≥0) : Function.Injective (samples H) := by
  intro f g h
  apply DFunLike.coe_injective
  exact (denseRange_denseSeq (Time H)).equalizer f.continuous g.continuous h

theorem samples_embedding (H : ℝ≥0) : MeasurableEmbedding (samples H) :=
  (continuous_samples H).measurableEmbedding (samples_injective H)

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (a : E → ℝ)

/-- Reconstruct a scalar continuous observable path from its dense
countable skeleton, with a fixed default outside the skeleton's Borel
range. This gives a Borel functional on ALL state paths, while agreeing
exactly with a(x(t)) whenever that observable path is continuous. -/
def observable (x : Path H E) : C(Time H, ℝ) :=
  Function.extend (samples H) id (fun _ ↦ 0) (fun n ↦ a (x (denseSeq (Time H) n)))

theorem measurable_observable (ha : Measurable a) : Measurable (observable H a) :=
  ((samples_embedding H).measurable_extend measurable_id measurable_const).comp
    (measurable_pi_lambda fun n ↦ ha.comp (ContinuousMap.measurable_eval _))

theorem observable_eq (x : Path H E) (hc : Continuous (fun t ↦ a (x t))) :
    observable H a x = ⟨fun t ↦ a (x t), hc⟩ :=
  (samples_injective H).extend_apply id (fun _ ↦ 0) ⟨fun t ↦ a (x t), hc⟩

theorem observable_nonneg (x : Path H E) (ha0 : ∀ t, 0 ≤ a (x t)) (t : Time H) :
    0 ≤ observable H a x t := by
  classical
  by_cases hr : ∃ Q : C(Time H, ℝ), samples H Q = fun n ↦ a (x (denseSeq (Time H) n))
  · obtain ⟨Q, hQ⟩ := hr
    have he : observable H a x = Q := by
      change Function.extend (samples H) id (fun _ ↦ 0)
        (fun n ↦ a (x (denseSeq (Time H) n))) = Q
      rw [← hQ]
      exact (samples_injective H).extend_apply id (fun _ ↦ 0) Q
    rw [he]
    refine (denseRange_denseSeq (Time H)).induction_on t
      (isClosed_le continuous_const Q.continuous) ?_
    intro n
    have hh := congrFun hQ n
    change Q (denseSeq (Time H) n) = a (x (denseSeq (Time H) n)) at hh
    rw [hh]
    exact ha0 _
  · have he : observable H a x = 0 := Function.extend_apply' id (fun _ ↦ 0) _ hr
    rw [he]
    exact le_rfl

def exit (R : ℝ) (x : Path H E) : Time H := time H id R (observable H a x)

theorem measurable_exit (ha : Measurable a) (R : ℝ) : Measurable (exit H a R) :=
  (measurable_time H id R continuous_id).comp (measurable_observable H a ha)

theorem exit_eq (R : ℝ) (x : Path H E) (hc : Continuous (fun t ↦ a (x t))) :
    exit H a R x = time H a R x := by
  rw [exit, observable_eq H a x hc]
  rfl

def stopped (R : ℝ) (x : Path H E) : Path H E := StoppedPathPasting.stopped H (exit H a R x) x

theorem measurable_stopped (ha : Measurable a) (R : ℝ) : Measurable (stopped H a R) :=
  (continuous_stopped H).measurable.comp ((measurable_exit H a ha R).prodMk measurable_id)

/-- Recover the same exit from the pasted state path. Only continuity
of the observable along the two actual paths is required; a itself
need not be continuous on the entire state space. -/
theorem exit_paste (R : ℝ) (x y : Path H E)
    (hc : Continuous (fun t ↦ a (x t)))
    (hp : Continuous (fun t ↦ a (paste H (exit H a R x) x y t))) :
    exit H a R (paste H (exit H a R x) x y) = exit H a R x := by
  rw [exit_eq H a R _ hp]
  rw [exit_eq H a R x hc]
  exact time_paste H a R x y
    (attained H a R x (isClosed_le continuous_const hc))

theorem stopped_paste (R : ℝ) (x y : Path H E)
    (hc : Continuous (fun t ↦ a (x t)))
    (hp : Continuous (fun t ↦ a (paste H (exit H a R x) x y t))) :
    stopped H a R (paste H (exit H a R x) x y) = stopped H a R x := by
  unfold stopped
  rw [exit_paste H a R x y hc hp]
  exact StoppedPathPasting.stopped_paste H (exit H a R x) x y

end SHEStochastic.BorelObservablePath
