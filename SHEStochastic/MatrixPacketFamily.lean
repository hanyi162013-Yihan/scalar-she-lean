module

public import SHEStochastic.MatrixDirectionEnergy
public import SHEStochastic.VectorHeatPackets
public import SHE.HaarHigherHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixPacketFamily
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixPhysicalColumnSmooth
open MatrixActualColumnCalculus MatrixDirectionBounds
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]
variable (F : List Bool → d → Physical (d := d)) (v : Domain (d := d)) (K : ℝ)
  (hbound : ∀ p i, ‖F p i‖ ≤ K * (Real.sqrt (childLength p))⁻¹ * localSize p v)

include hbound in
theorem generation (n : ℕ) (i : d) :
    (∑ x : Grid n, ‖F (leafPath n x) i‖ ^ 2) ≤
      2 * K ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ)) * ‖v‖ ^ 2 := by
  let A := K ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ x : Grid n, A * localSize (leafPath n x) v ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hh := pow_le_pow_left₀ (norm_nonneg _) (hbound (leafPath n x) i) 2
      have hs : (Real.sqrt (childLength (leafPath n x)))⁻¹ ^ 2 = (((2 ^ (n+1) : ℕ) : ℝ)) := by
        rw [inv_pow, Real.sq_sqrt (childLength_pos _).le]
        simp only [childLength, leafPath_length, inv_inv]
      exact hh.trans_eq (by rw [mul_pow, mul_pow, hs])
    _ = A * ∑ x : Grid n, localSize (leafPath n x) v ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (2 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left (MatrixDirectionEnergy.generation n v) hA
    _ = _ := by dsimp [A]; ring

variable (hsupport : ∀ p i, ∀ᵐ x ∂μ, x ∉ nodeCell p → F p i x = 0)
  (hmean : ∀ p i, (∫ x, F p i x ∂μ) = 0)

include hbound hsupport hmean in
theorem heat_generation {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    (∑ x : Grid n, ∑ i : d, ‖VectorHeat.heat t (F (leafPath n x) i)‖ ^ 2) ≤
      (2 * (Fintype.card d : ℝ) * packetHeatConstant * K ^ 2 * ‖v‖ ^ 2) *
      (((2 ^ (n+1) : ℕ) : ℝ)) * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t) := by
  let a := packetHeatConstant * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t)
  have ha : 0 ≤ a := mul_nonneg (zero_le_one.trans packetHeatConstant_one_le)
    (le_min zero_le_one (by positivity))
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : d, a * (2 * K ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ)) * ‖v‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ x : Grid n, a * ‖F (leafPath n x) i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          simpa only [a, nodeLength, leafPath_length] using VectorHeatPackets.packet_min ht ht1
            (leafPath n x) (F (leafPath n x) i) (hsupport _ _) (hmean _ _)
        _ = a * (∑ x : Grid n, ‖F (leafPath n x) i‖ ^ 2) := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (generation F v K hbound n i) ha
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [a]; ring

include hbound hsupport hmean in
/-- Shared generation summation for actual matrix derivative packets
and signed column differences; all geometric input is literal support,
mean zero, and the proved localized one-input norm estimate. -/
theorem energy {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Summable (fun p : List Bool => ∑ i : d, ‖VectorHeat.heat t (F p i)‖ ^ 2) ∧
      (∑' p : List Bool, ∑ i : d, ‖VectorHeat.heat t (F p i)‖ ^ 2) ≤
        4 * (Fintype.card d : ℝ) * packetHeatConstant * K ^ 2 *
          (DyadicTransport.smoothingConstant (1/2)) ^ 2 * t ^ (-(1/2 : ℝ)) * ‖v‖ ^ 2 := by
  have hP : 0 ≤ packetHeatConstant := zero_le_one.trans packetHeatConstant_one_le
  have hh := packet_generation_sum ht ht1
    (by positivity : 0 ≤ 2 * (Fintype.card d : ℝ) * packetHeatConstant * K ^ 2 * ‖v‖ ^ 2)
    (fun p : List Bool => ∑ i : d, ‖VectorHeat.heat t (F p i)‖ ^ 2)
    (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (fun n => heat_generation F v K hbound hsupport hmean ht ht1 n)
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

end SHEStochastic.MatrixPacketFamily
