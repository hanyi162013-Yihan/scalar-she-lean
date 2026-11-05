module

public import SHEStochastic.WeakLimitProbabilityTools
public import SHEStochastic.JointStateDriverPath
public import SHEStochastic.FiniteScalarIto
public import SHE.CanonicalStateDriverFiltration
public import Mathlib.Topology.Metrizable.Uniformity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.WeakLimitCanonicalBrownian
open MeasureTheory ProbabilityTheory Filter SHE
open SHE.CanonicalStateDriverFiltration StoppedPathPasting
open scoped NNReal Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι] (H : ℝ≥0)

abbrev Space := CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H

theorem continuous_history (t : ℝ≥0) :
    Continuous (history (E := E) (ι := ι) H t) := by
  have he : history (E := E) (ι := ι) H t = fun x ↦
      JointStateDriverPath.unpack H
        (stopped H (clock H t) (JointStateDriverPath.pack H x)) := by
    funext x
    rfl
  rw [he]
  exact (JointStateDriverPath.continuous_unpack H).comp
    ((continuous_stopped H).comp
      (continuous_const.prodMk (JointStateDriverPath.continuous_pack H)))

theorem continuous_coordinate (i : ι) (t : ℝ≥0) :
    Continuous (coordinate (E := E) H i t) :=
  (continuous_eval_const (clock H t)).comp ((continuous_apply i).comp continuous_snd)

def observation {n : ℕ} (a : Fin n → ι) (t : Fin n → ℝ≥0) (x : Space (E := E) (ι := ι) H) :
    WordRecursion.State n := WithLp.toLp 2 (fun i ↦ coordinate H (a i) (t i) x)

theorem continuous_observation {n : ℕ} (a : Fin n → ι) (t : Fin n → ℝ≥0) :
    Continuous (observation (E := E) H a t) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp
    (continuous_pi fun i ↦ continuous_coordinate H (a i) (t i))

def increment {n : ℕ} (a : Fin n → ι) (s t : ℝ≥0) (x : Space (E := E) (ι := ι) H) :
    WordRecursion.State n := WithLp.toLp 2
      (fun i ↦ coordinate H (a i) t x - coordinate H (a i) s x)

theorem continuous_increment {n : ℕ} (a : Fin n → ι) (s t : ℝ≥0) :
    Continuous (increment (E := E) H a s t) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp (continuous_pi fun i ↦
    (continuous_coordinate H (a i) t).sub (continuous_coordinate H (a i) s))

/-- Brownian coordinates on joint state/driver path space survive weak
convergence with independence from the ENTIRE state and driver history.
Thus the weak limit supplies the same native integration construction;
neither a new Levy nor a martingale representation theorem is assumed. -/
def family (P : ℕ → ProbabilityMeasure (Space (E := E) (ι := ι) H))
    (Q : ProbabilityMeasure (Space (E := E) (ι := ι) H))
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ k n (a : Fin n → ι),
      FiniteBrownianLawOn (filtration (E := E) (ι := ι) H) (P k : Measure _) H
        (fun i ↦ coordinate H (a i)) (fun i j ↦ if a i = a j then 1 else 0)) :
    FiniteScalarIto.Family (filtration (E := E) (ι := ι) H) (Q : Measure _) H ι := by
  letI : MetricSpace (Space (E := E) (ι := ι) H) :=
    TopologicalSpace.metrizableSpaceMetric _
  refine ⟨⟨coordinate H, coordinate_adapted H, ?_⟩, coordinate_continuous H⟩
  intro n a
  constructor
  · intro t ht
    exact WeakLimitProbabilityTools.hasLaw P Q hlim (observation H a t)
      (continuous_observation H a t) _ (fun k ↦ (hP k n a).1 t ht)
  · intro s t hst ht
    have hi (k : ℕ) : IndepFun (history (E := E) (ι := ι) H s)
        (increment H a s t) (P k : Measure _) := (hP k n a).2 s t hst ht |>.symm
    exact (WeakLimitProbabilityTools.indepFun P Q hlim (history H s) (increment H a s t)
      (continuous_history H s) (continuous_increment H a s t) hi).symm

end SHEStochastic.WeakLimitCanonicalBrownian
