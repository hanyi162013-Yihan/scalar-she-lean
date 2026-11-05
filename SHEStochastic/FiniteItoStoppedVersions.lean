module

public import SHEStochastic.FiniteItoStochasticTerms
public import SHE.StoppedInputAlgebra
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.FiniteItoStoppedVersions
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.GaussianItoTest
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

def stopped (Y : ℝ≥0 × Ω → State n) (t : ℝ≥0) (p : ℝ≥0 × Ω) : State n :=
  Y (min p.1 t, p.2)

theorem continuous (Y : ℝ≥0 × Ω → State n)
    (hc : ∀ ω, Continuous (fun r ↦ Y (r, ω))) (t : ℝ≥0) (ω : Ω) :
    Continuous (fun r ↦ stopped Y t (r, ω)) := (hc ω).comp (continuous_id.min continuous_const)

theorem predictable (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun r ↦ Y (r, ω))) (t : ℝ≥0) :
    StronglyMeasurable[F.predictable] (stopped Y t) := by
  have ha : StronglyAdapted F (fun r ω ↦ Y (r, ω)) :=
    (show IsStronglyPredictable F (fun r ω ↦ Y (r, ω)) from hY).stronglyAdapted
  change IsStronglyPredictable F (fun r ω ↦ stopped Y t (r, ω))
  apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · intro r
    exact (ha (min r t)).mono (F.mono (min_le_left _ _))
  · intro ω r
    exact (continuous Y hc t ω).continuousWithinAt

/-- Stopping the continuous version and the original predictable rows
commutes with the very same terminal integral. -/
theorem represents_random (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n)
    (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ r : ℝ≥0, r ≤ H → (fun ω ↦ Y (r, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) R r ω))
    (t r : ℝ≥0) (hrH : r ≤ H) :
    (fun ω ↦ stopped Y t (r, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H J (z ω) (fun i ↦ stop F μ H t (R i)) r ω) := by
  have he := hRep (min r t) ((min_le_left _ _).trans hrH)
  change (fun ω ↦ Y (min r t, ω)) =ᵐ[μ] _
  refine he.trans (Filter.Eventually.of_forall fun ω ↦ ?_)
  ext i
  change z ω i + J.integral (stop F μ H (min r t) (R i)) ω =
    z ω i + J.integral (stop F μ H r (stop F μ H t (R i))) ω
  rw [StoppedInputAlgebra.stop_stop]

theorem represents (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : State n)
    (Y : ℝ≥0 × Ω → State n)
    (hRep : ∀ r : ℝ≥0, r ≤ H → (fun ω ↦ Y (r, ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H J z R r)
    (t r : ℝ≥0) (hrH : r ≤ H) :
    (fun ω ↦ stopped Y t (r, ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H J z (fun i ↦ stop F μ H t (R i)) r := by
  exact represents_random J R (fun _ ↦ z) Y hRep t r hrH

/-- The full horizon already contains all of an original predictable
input; its final singleton carries zero time measure. -/
theorem stop_horizon (u : Process (E := C) F μ H) : stop F μ H H u = u := by
  have ht : ∀ᵐ r ∂timeMeasure H, r < H := by
    filter_upwards [timeMeasure_ae_mem H, (timeMeasure H).ae_ne H] with r hr hne
    exact lt_of_le_of_ne hr.2 hne
  have hp : ∀ᵐ p : ℝ≥0 × Ω ∂energyMeasure μ H, p.1 < H :=
    Measure.quasiMeasurePreserving_fst.ae ht
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  filter_upwards [stop_ae F μ H H u, hp] with p hs ht
  rw [hs, Set.indicator_of_mem (show p ∈ before (Ω := Ω) H from by exact_mod_cast ht)]

end SHEStochastic.FiniteItoStoppedVersions
