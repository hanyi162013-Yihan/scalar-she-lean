module

public import SHEStochastic.ContinuousCoordinateLaw
public import SHEStochastic.FiniteScalarIto
public import SHE.BrownianFuturePath
public import SHE.BrownianShiftedFiniteLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeBrownianPathLaw
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal

variable {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable ι] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F' : Filtration ℝ≥0 ‹MeasurableSpace Ω'›} {ν : Measure Ω'} [IsProbabilityMeasure ν] {H : ℝ≥0}

/-- All actual native Brownian families have the same centered path
law, even when produced by different solution-dependent rotations or
living on different probability spaces. -/
theorem map_eq (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family F' ν H ι) :
    μ.map (BrownianFuturePath.value P.W P.continuous 0 H) =
      ν.map (BrownianFuturePath.value Q.W Q.continuous 0 H) := by
  apply ContinuousCoordinateLaw.map_eq μ ν _ _
    (BrownianFuturePath.measurable F P.W P.continuous P.adapted 0 H)
    (BrownianFuturePath.measurable F' Q.W Q.continuous Q.adapted 0 H)
  intro n a
  let t (i : Fin n) : ℝ≥0 := (a i).2.val.toNNReal
  have ht (i : Fin n) : t i ≤ H := by
    simpa only [t, Real.toNNReal_coe] using Real.toNNReal_le_toNNReal (a i).2.property.2
  have hp := BrownianShiftedFiniteLaw.law F μ H P.W P.law 0 H (by simp) (fun i ↦ (a i).1) t ht
  have hq := BrownianShiftedFiniteLaw.law F' ν H Q.W Q.law 0 H (by simp) (fun i ↦ (a i).1) t ht
  have hmP : Measurable (fun sample ↦ (WithLp.toLp 2 (fun i : Fin n ↦
      P.W (a i).1 (0+t i) sample - P.W (a i).1 0 sample) : WordRecursion.State n)) :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr fun i ↦
      (FiniteScalarIto.measurable_coordinate P.toCoordinates (a i).1 (0+t i)).sub
        (FiniteScalarIto.measurable_coordinate P.toCoordinates (a i).1 0))
  have hmQ : Measurable (fun sample ↦ (WithLp.toLp 2 (fun i : Fin n ↦
      Q.W (a i).1 (0+t i) sample - Q.W (a i).1 0 sample) : WordRecursion.State n)) :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr fun i ↦
      (FiniteScalarIto.measurable_coordinate Q.toCoordinates (a i).1 (0+t i)).sub
        (FiniteScalarIto.measurable_coordinate Q.toCoordinates (a i).1 0))
  have he := congrArg (fun m : Measure (WordRecursion.State n) ↦ m.map WithLp.ofLp)
    (hp.map_eq.trans hq.map_eq.symm)
  rw [Measure.map_map (WithLp.measurable_ofLp 2 (Fin n → ℝ)) hmP,
    Measure.map_map (WithLp.measurable_ofLp 2 (Fin n → ℝ)) hmQ] at he
  exact he

end SHEStochastic.NativeBrownianPathLaw
