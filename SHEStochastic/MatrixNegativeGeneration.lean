module

public import SHEStochastic.MatrixNegativeJets
public import SHEStochastic.MatrixNegativeLocalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHEStochastic.MatrixNegativeGeneration
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def localization (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) : ℝ :=
  (MatrixNegativeLocalization.exists_generation (d := d) hρ hρhalf).choose

theorem localization_pos (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    0 < localization (d := d) ρ hρ hρhalf :=
  (MatrixNegativeLocalization.exists_generation (d := d) hρ hρhalf).choose_spec.1

def constant (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) : ℝ :=
  1 + 4 * (Fintype.card d : ℝ) ^ 2 * negativeSlotConstant ρ ^ 2 * MatrixNegativeJets.orderConstant P ρ k ^ 2 *
    localization (d := d) ρ hρ hρhalf

theorem constant_pos (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) :
    0 < constant P ρ hρ hρhalf k := by
  have hL := localization_pos (d := d) ρ hρ hρhalf
  unfold constant
  positivity

/-- Actual matrix Haar higher jets obey the negative-input generation
estimate on every grid. Both state components and all physical output
components are counted, with only one negative Sobolev direction. -/
theorem bound {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (P : Profile d) (n : ℕ) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    (∑ x : Grid n, ∑ i : d, ∑ r : d,
      ‖operator Λ ρ hΛ hρ.le (component r
        (MatrixPhysicalJetStructure.jetColumn P (leafPath n x) i (v :: w)))‖ ^ 2) ≤
      constant P ρ hρ hρhalf w.length * (((2 ^ (n+1) : ℕ) : ℝ)) *
        MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight B w ^ 2 := by
  let N := (((2 ^ (n+1) : ℕ) : ℝ))
  let A := 4 * N * negativeSlotConstant ρ ^ 2 * MatrixNegativeJets.orderConstant P ρ w.length ^ 2 *
    MatrixJetClosure.weight B w ^ 2
  let D := (Fintype.card d : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp [A, N]; positivity
  have hD : 0 ≤ D := sq_nonneg _
  have hLocal := (MatrixNegativeLocalization.exists_generation (d := d) hρ hρhalf).choose_spec.2 Λ hΛ n v
  have hE : 0 ≤ MatrixNegativeLocalization.energy Λ ρ v := MatrixNegativeLocalization.energy_nonneg hΛ v
  calc
    _ ≤ ∑ x : Grid n, ∑ i : d, ∑ r : d, A * localNorm (leafPath n x) Λ ρ hΛ hρ.le v ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro r hr
      have hh := pow_le_pow_left₀ (norm_nonneg _)
        (MatrixNegativeJets.one_input hΛ hρ hρhalf P (leafPath n x) i r v w B hB hRest) 2
      have hs : (Real.sqrt (childLength (leafPath n x)))⁻¹ ^ 2 = N := by
        rw [inv_pow, Real.sq_sqrt (childLength_pos _).le]
        simp only [childLength, leafPath_length, inv_inv, N]
      exact hh.trans_eq (by simp only [mul_pow, hs]; dsimp [A]; ring)
    _ = D * A * ∑ x : Grid n, localNorm (leafPath n x) Λ ρ hΛ hρ.le v ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [D]
      ring
    _ ≤ D * A * (localization (d := d) ρ hρ hρhalf * MatrixNegativeLocalization.energy Λ ρ v) :=
      mul_le_mul_of_nonneg_left hLocal (mul_nonneg hD hA)
    _ = (4 * D * negativeSlotConstant ρ ^ 2 * MatrixNegativeJets.orderConstant P ρ w.length ^ 2 *
        localization (d := d) ρ hρ hρhalf) * (N * MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight B w ^ 2) := by
      dsimp [A]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right (show _ ≤ constant P ρ hρ hρhalf w.length from by unfold constant; dsimp [D]; linarith)
        (mul_nonneg (mul_nonneg (by dsimp [N]; positivity) hE) (sq_nonneg _)) |>.trans_eq
      ring

end SHEStochastic.MatrixNegativeGeneration
