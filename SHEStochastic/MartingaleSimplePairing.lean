module

public import SHEStochastic.MartingaleCrossPairing
public import SHEStochastic.FiniteScalarIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MartingaleSimplePairing
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι)

/-- Two square-integrable martingales with the same cross-compensator
against an actual Brownian coordinate have identical terminal pairings
with every original bounded predictable simple integral. -/
theorem pairing (M N : ℝ≥0 → Ω → ℝ) (hM : Martingale M F μ) (hN : Martingale N F μ)
    (hM2 : ∀ r, r ≤ H → MemLp (M r) 2 μ) (hN2 : ∀ r, r ≤ H → MemLp (N r) 2 μ)
    (i : ι) (A : ℝ≥0 → Ω → ℝ)
    (hCrossM : Martingale (fun r sample ↦ M r sample * P.W i r sample - A r sample) F μ)
    (hCrossN : Martingale (fun r sample ↦ N r sample * P.W i r sample - A r sample) F μ)
    (V : FiniteScalarIto.Simple F H) :
    (∫ sample, M H sample * FiniteScalarIto.simpleValue P.toCoordinates i V sample ∂μ) =
      ∫ sample, N H sample * FiniteScalarIto.simpleValue P.toCoordinates i V sample ∂μ := by
  classical
  let q (p : ℝ≥0 × ℝ≥0) (sample : Ω) := V.val.value p sample * (P.W i p.2 sample-P.W i p.1 sample)
  have hiM (p) (hp : p ∈ V.val.value.support) : Integrable (fun sample ↦ M H sample * q p sample) μ :=
    (hM2 H le_rfl).integrable_mul (FiniteScalarIto.memLp_term P.toCoordinates i V p hp)
  have hiN (p) (hp : p ∈ V.val.value.support) : Integrable (fun sample ↦ N H sample * q p sample) μ :=
    (hN2 H le_rfl).integrable_mul (FiniteScalarIto.memLp_term P.toCoordinates i V p hp)
  change (∫ sample, M H sample * (∑ p ∈ V.val.value.support, q p sample) ∂μ) =
    ∫ sample, N H sample * (∑ p ∈ V.val.value.support, q p sample) ∂μ
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hiM, integral_finsetSum _ hiN]
  apply Finset.sum_congr rfl
  intro p hp
  have hB : StronglyAdapted F (P.W i) := fun r ↦ (P.adapted i r).stronglyMeasurable
  have hB2 (r : ℝ≥0) (hr : r ≤ H) : MemLp (P.W i r) 2 μ :=
    BrownianCoordinates.memLp_eval F μ H P.W P.law i r hr 2 (by simp)
  have hm := MartingaleCrossPairing.cell μ F M (P.W i) A hM hB hCrossM H hM2 hB2 p.1 p.2
    (V.val.le_of_mem_support_value p hp) (V.property p hp) (V.val.value p)
    (V.val.measurable_value p).stronglyMeasurable V.val.valueBound (V.val.value_le_valueBound p)
  have hn := MartingaleCrossPairing.cell μ F N (P.W i) A hN hB hCrossN H hN2 hB2 p.1 p.2
    (V.val.le_of_mem_support_value p hp) (V.property p hp) (V.val.value p)
    (V.val.measurable_value p).stronglyMeasurable V.val.valueBound (V.val.value_le_valueBound p)
  exact hm.trans hn.symm

end SHEStochastic.MartingaleSimplePairing
