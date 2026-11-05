module
public import SHE.BoundedRowStepInputs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
namespace SHE.BoundedRowStepInputs
open MeasureTheory Set PredictableL2 ApproximationCells Filter
open scoped NNReal ENNReal Topology
variable {Ω E C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [NormedAddCommGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H q : ℝ≥0) (R : Iic q×E→C) (hR : Continuous R)
variable (U : ℝ≥0→Ω→E) (hUa : StronglyAdapted 𝓕 U)
variable (M : ℝ) (hb : ∀p,‖R p‖≤M)

/-- The genuine predictable step input has exactly the previously
estimated left-frozen raw row; deterministic cell endpoints are null. -/
theorem input_frozen_ae (n : ℕ) : input 𝓕 μ H q R hR U hUa M hb n=ᵐ[energyMeasure μ H]
    BoundedContinuousRowFreezing.value q R U n := by
  have hpos : ∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,0<p.1 :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure_ae_mem H).mono (fun _ ht=>ht.1))
  have hne : ∀ᵐp:ℝ≥0×Ω∂energyMeasure μ H,p.1≠q :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne q)
  filter_upwards [input_ae 𝓕 μ H q R hR U hUa M hb n,hpos,hne] with p hi hp0 hn
  rw [hi]
  by_cases hp : p.1<q
  · have he : (∑k∈Finset.Icc 1 (index n q),PredictableSteps.step (time q n (k-1)) (time q n k)
        (coefficient q R U n k) p)=ApproximationCells.sum n q (coefficient q R U n) p := by
      apply Finset.sum_congr rfl
      intro k hk
      have ht : p.1∈Ioc (time q n (k-1)) (time q n k) ↔p.1∈Ioc (point n (k-1)) (point n k) := by
        simp only [time,mem_Ioc,min_lt_iff,le_min_iff,not_lt.mpr hp.le,or_false,hp.le,and_true]
      simp only [PredictableSteps.step,ht]
    rw [he,ApproximationCells.sum_at n hp0 hp.le]
    have hleft : LeftFrozenHaarKernel.past n p.1=point n (index n p.1-1) := by
      change (ApproximationClock.left n (p.1:ℝ)).toNNReal=_
      rw [left_eq_point n hp0,Real.toNNReal_coe]
    have hlq : point n (index n p.1-1)≤q := by
      rw [←hleft]
      exact (LeftFrozenHaarKernel.past_le n p.1).trans hp.le
    simp only [BoundedContinuousRowFreezing.value,ite_eq_left hp,coefficient,time,
      BoundedContinuousRowFreezing.time,hleft,min_eq_left hlq]
  · have hqp : q<p.1 := lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hn)
    rw [BoundedContinuousRowFreezing.value,ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro k hk
    unfold PredictableSteps.step
    apply ite_eq_right
    intro ht
    exact (not_le.mpr hqp) (ht.2.trans (min_le_right _ _))
end SHE.BoundedRowStepInputs
