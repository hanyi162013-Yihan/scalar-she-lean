module

public import SHEStochastic.MatrixHeatKernelApproximation
public import SHE.ApproximationCells

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixHeatCellInput
open MeasureTheory Set SHE SHE.FiniteHaar SHE.PredictableL2 SHE.ApproximationClock SHE.ApproximationCells
  MatrixInfiniteHaar MatrixAnalyticKernel
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d)
    (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

def cell (n k : ℕ) (p : ℝ≥0 × Ω) : MatrixHaarKernel.Columns (d := d) :=
  if k=0 then 0 else if p.1 ≤ point n (k-1) then kernel ((point n k : ℝ)-(p.1 : ℝ)) (Q p) else 0

include hQ in
theorem predictable (n k : ℕ) : StronglyMeasurable[F.predictable] (cell Q n k) := by
  by_cases hk : k=0
  · subst k
    change StronglyMeasurable[F.predictable] (fun _ : ℝ≥0 × Ω => (0 : MatrixHaarKernel.Columns (d := d)))
    exact stronglyMeasurable_const
  · have hset : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | p.1 ≤ point n (k-1)} :=
      measurableSet_le (PredictableClock.time_measurable F) measurable_const
    have hm := (MatrixAnalyticKernel.predictable F Q hQ (point n k)).indicator
      (s := {p : ℝ≥0 × Ω | p.1 ≤ point n (k-1)}) hset
    have he : cell Q n k = {p : ℝ≥0 × Ω | p.1 ≤ point n (k-1)}.indicator
        (fun p => kernel ((point n k : ℝ)-(p.1 : ℝ)) (Q p)) := by
      funext p
      simp only [cell,if_neg hk,Set.indicator_apply,Set.mem_setOf_eq]
    rw [he]
    exact hm

include hU hUpper in
theorem bound (n k : ℕ) (p : ℝ≥0 × Ω) :
    ‖cell Q n k p‖ ≤ Real.sqrt (gapConstant d U (delta n)) := by
  have hC := gapConstant_nonneg hU (delta_pos n) (d := d)
  by_cases hk : k=0
  · simp only [cell,if_pos hk,norm_zero,Real.sqrt_nonneg]
  · by_cases hp : p.1 ≤ point n (k-1)
    · have hg : (point n k : ℝ)-(point n (k-1) : ℝ)=delta n := by
        change delta n*(k : ℝ)-delta n*((k-1 : ℕ) : ℝ)=delta n
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk),Nat.cast_one]
        ring
      have hage : delta n ≤ (point n k : ℝ)-(p.1 : ℝ) := by
        have hpp : (p.1 : ℝ) ≤ point n (k-1) := by exact_mod_cast hp
        linarith
      rw [cell,if_neg hk,if_pos hp]
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hC]
      exact gap_bound (delta_pos n) hage (Q p) (hUpper p)
    · simp only [cell,if_neg hk,if_neg hp,norm_zero,Real.sqrt_nonneg]

include hU hUpper hQ in
theorem memLp (n k : ℕ) : @MemLp _ _ F.predictable _ _ (cell Q n k) 2
    ((energyMeasure μ H).trim (predictable_le_product F)) := by
  letI : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  letI : IsFiniteMeasure ((energyMeasure μ H).trim (predictable_le_product F)) := inferInstance
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact MemLp.of_bound (predictable F Q hQ n k).aestronglyMeasurable
    (Real.sqrt (gapConstant d U (delta n))) (Filter.Eventually.of_forall (bound U hU Q hUpper n k))

/-- Actual adapted finite-cell Itô inputs, on the original full horizon.
No time-regularity or integrability premise is left to the caller. -/
def input (n k : ℕ) : Process (E := MatrixHaarKernel.Columns (d := d)) F μ H :=
  (memLp F μ H U hU Q hUpper hQ n k).toLp (cell Q n k)

theorem input_ae (n k : ℕ) :
    input F μ H U hU Q hUpper hQ n k =ᵐ[energyMeasure μ H] cell Q n k :=
  ae_eq_of_ae_eq_trim (memLp F μ H U hU Q hUpper hQ n k).coeFn_toLp

theorem stopped (n k : ℕ) : ∀ᵐ p ∂energyMeasure μ H,
    point n (k-1) < p.1 → input F μ H U hU Q hUpper hQ n k p=0 := by
  filter_upwards [input_ae F μ H U hU Q hUpper hQ n k] with p hp hpt
  rw [hp]
  by_cases hk : k=0 <;> simp only [cell,hk,if_true,if_false,if_neg (not_le.mpr hpt)]

theorem input_at (n : ℕ) {t : ℝ≥0} (ht : 0 < t) (htH : t ≤ H) :
    input F μ H U hU Q hUpper hQ n (index n t) =ᵐ[energyMeasure μ H]
      fun p : ℝ≥0 × Ω => MatrixHeatKernelApproximation.approximant n t p.1 (Q p) := by
  have hk : index n t ≠ 0 := by have := (Finset.mem_Icc.mp (index_mem n ht htH)).1; omega
  filter_upwards [input_ae F μ H U hU Q hUpper hQ n (index n t)] with p hp
  rw [hp]
  unfold cell MatrixHeatKernelApproximation.approximant
  rw [if_neg hk,right_eq_point,left_eq_point n ht]
  have he : p.1 ≤ point n (index n t-1) ↔ (p.1 : ℝ) ≤ point n (index n t-1) := by exact_mod_cast Iff.rfl
  simp only [he]

end SHEStochastic.MatrixHeatCellInput
