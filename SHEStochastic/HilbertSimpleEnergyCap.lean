module

public import SHEStochastic.HilbertCellMesh
public import SHEStochastic.HilbertSimpleGaussian
public import SHEStochastic.SimpleEnergyCapAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertSimpleEnergyCap
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0}
  (V : HilbertSimpleInputs.bounded (E := C) F H)

local notation "T" => marshalPart F H V.val
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

def cumulative (k : ℕ) (ω : Ω) : ℝ :=
  SimpleEnergyCapAlgebra.accumulated (fun j ↦ HilbertSimpleGaussian.variance V j ω) k

theorem variance_nonneg (k : ℕ) (ω : Ω) : 0 ≤ HilbertSimpleGaussian.variance V k ω :=
  mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)

theorem variance_adapted (k : ℕ) :
    StronglyMeasurable[F (T k)] (HilbertSimpleGaussian.variance V k) :=
  ((stronglyMeasurable_marshalMult F H V.val k).norm.pow 2).const_mul _

theorem cumulative_adapted (k : ℕ) : StronglyMeasurable[F (T k)] (cumulative V k) := by
  change StronglyMeasurable[F (T k)]
    (fun ω ↦ ∑ j ∈ Finset.range k, HilbertSimpleGaussian.variance V j ω)
  apply Finset.stronglyMeasurable_fun_sum
  intro j hj
  exact (variance_adapted V j).mono
    (F.mono (marshalPart_mono F H V.val V.property (Finset.mem_range.mp hj).le))

def coefficient (K : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  SimpleEnergyCapAlgebra.factor K (cumulative V k ω) (HilbertSimpleGaussian.variance V k ω)

theorem coefficient_adapted (K : ℝ) (k : ℕ) : StronglyMeasurable[F (T k)] (coefficient V K k) := by
  have hf : Measurable (fun p : ℝ × ℝ ↦ SimpleEnergyCapAlgebra.factor K p.1 p.2) := by
    unfold SimpleEnergyCapAlgebra.factor SimpleEnergyCapAlgebra.allocation
    fun_prop
  exact (hf.comp ((cumulative_adapted V k).measurable.prodMk
    (variance_adapted V k).measurable)).stronglyMeasurable

theorem coefficient_nonneg (K : ℝ) (k : ℕ) (ω : Ω) : 0 ≤ coefficient V K k ω :=
  SimpleEnergyCapAlgebra.factor_nonneg _ _ _

theorem coefficient_le_one (K : ℝ) (k : ℕ) (ω : Ω) : coefficient V K k ω ≤ 1 :=
  SimpleEnergyCapAlgebra.factor_le_one _ _ (variance_nonneg V k ω)

def row (K : ℝ) (k : ℕ) (ω : Ω) : C := coefficient V K k ω • marshalMult F H V.val k ω

theorem row_adapted (K : ℝ) (k : ℕ) : StronglyMeasurable[F (T k)] (row V K k) :=
  (coefficient_adapted V K k).smul (stronglyMeasurable_marshalMult F H V.val k)

theorem row_bound (K : ℝ) (k : ℕ) (ω : Ω) :
    ‖row V K k ω‖ ≤ (V.val.value.support.card : ℝ) * V.val.valueBound := by
  rw [row, norm_smul, Real.norm_of_nonneg (coefficient_nonneg V K k ω)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (coefficient_le_one V K k ω)).trans
    (marshalMult_norm_le F H V.val k ω)

/-- Predictable clipping on the existing common mesh. The coefficient
for the current cell uses its past-known variance and accumulated past
energy, and never uses future rows. -/
def cap (K : ℝ) (N : ℕ) : HilbertSimpleInputs.bounded (E := C) F H :=
  HilbertCellMesh.assemble V N (row V K) (row_adapted V K)
    ((V.val.value.support.card : ℝ) * V.val.valueBound) (row_bound V K)

theorem row_energy (K : ℝ) (k : ℕ) (ω : Ω) :
    (((T (k + 1) : ℝ≥0) : ℝ) - T k) * ‖row V K k ω‖ ^ 2 =
      coefficient V K k ω ^ 2 * HilbertSimpleGaussian.variance V k ω := by
  rw [row, norm_smul, Real.norm_of_nonneg (coefficient_nonneg V K k ω), mul_pow,
    HilbertSimpleGaussian.variance, NNReal.coe_sub
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))]
  ring

theorem cumulative_eq_energy (N : ℕ) (hN : T N = H) (ω : Ω) :
    cumulative V N ω = ∫ r, ‖V.val r ω‖ ^ 2 ∂νt := by
  change (∑ k ∈ Finset.range N, HilbertSimpleGaussian.variance V k ω) = _
  have he (k : ℕ) : HilbertSimpleGaussian.variance V k ω =
      (((T (k + 1) : ℝ≥0) : ℝ) - T k) * ‖marshalMult F H V.val k ω‖ ^ 2 := by
    rw [HilbertSimpleGaussian.variance, NNReal.coe_sub
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))]
  simp_rw [he]
  exact HilbertSimplePartition.energy_sum V hN ω

theorem cap_energy_le (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : T N = H) (ω : Ω) :
    (∫ r, ‖(cap V K N).val r ω‖ ^ 2 ∂νt) ≤ min (∫ r, ‖V.val r ω‖ ^ 2 ∂νt) K := by
  have hb := HilbertCellMesh.assemble_energy_le V N hN (row V K) (row_adapted V K)
    _ (row_bound V K) ω
  simp only [row_energy] at hb
  have he := SimpleEnergyCapAlgebra.energy_sum (fun k ↦ HilbertSimpleGaussian.variance V k ω)
    (fun k ↦ variance_nonneg V k ω) K hK N
  change (∑ k ∈ Finset.range N, coefficient V K k ω ^ 2 * HilbertSimpleGaussian.variance V k ω) =
    min (cumulative V N ω) K at he
  rw [he, cumulative_eq_energy V N hN ω] at hb
  exact hb

theorem row_loss (K : ℝ) (k : ℕ) (ω : Ω) :
    (((T (k + 1) : ℝ≥0) : ℝ) - T k) *
      ‖marshalMult F H V.val k ω - row V K k ω‖ ^ 2 =
      (1 - coefficient V K k ω) ^ 2 * HilbertSimpleGaussian.variance V k ω := by
  rw [row, show marshalMult F H V.val k ω - coefficient V K k ω •
      marshalMult F H V.val k ω =
      (1 - coefficient V K k ω) • marshalMult F H V.val k ω by
        rw [sub_smul, one_smul], norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    HilbertSimpleGaussian.variance, NNReal.coe_sub
      (marshalPart_mono F H V.val V.property (Nat.le_succ k))]
  ring

/-- The loss in squared time norm is at most the removed energy. -/
theorem cap_loss_le (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : T N = H) (ω : Ω) :
    (∫ r, ‖V.val r ω - (cap V K N).val r ω‖ ^ 2 ∂νt) ≤
      (∫ r, ‖V.val r ω‖ ^ 2 ∂νt) - min (∫ r, ‖V.val r ω‖ ^ 2 ∂νt) K := by
  have hb := HilbertCellMesh.assemble_loss_le V N hN (row V K) (row_adapted V K)
    _ (row_bound V K) ω
  simp only [row_loss] at hb
  have he := SimpleEnergyCapAlgebra.total_loss_le
    (fun k ↦ HilbertSimpleGaussian.variance V k ω)
    (fun k ↦ variance_nonneg V k ω) K hK N
  change (∑ k ∈ Finset.range N, (1 - coefficient V K k ω) ^ 2 *
    HilbertSimpleGaussian.variance V k ω) ≤
      cumulative V N ω - min (cumulative V N ω) K at he
  rw [cumulative_eq_energy V N hN ω] at he
  exact hb.trans he

end SHEStochastic.HilbertSimpleEnergyCap
