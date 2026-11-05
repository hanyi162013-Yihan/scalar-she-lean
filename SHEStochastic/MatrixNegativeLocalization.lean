module

public import SHEStochastic.MatrixNegativeEntries

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixNegativeLocalization
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

def energy (Λ ρ : ℝ) (v : Domain (d := d)) : ℝ :=
  ∑ r : d, ∑ j : d, StepInput.negativeEnergy 1 Λ ρ (realEmbed (entry r j v.val))

theorem energy_nonneg {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (v : Domain (d := d)) : 0 ≤ energy Λ ρ v := by
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro j hj
  rw [← NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
  unfold NegativeNash.energy
  positivity

theorem localNorm_entries (p : List Bool) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : Domain (d := d)) :
    localNorm p Λ ρ hΛ hρ v = ∑ r : d, ∑ j : d,
      SHE.FiniteHaar.localNegativeNorm p Λ ρ hΛ hρ (realEmbed (entry r j v.val)) := by
  unfold localNorm MatrixTransformedJets.localSize transformedSize
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  change ‖besselHalf Λ ρ hΛ hρ (realEmbed (entry r j
      (MatrixPhysicalColumnMap.restriction (cellSet (p.length+1) (bottomLeaf p false))
        (measurableSet_cellSet _ _) v.val)))‖ +
    ‖besselHalf Λ ρ hΛ hρ (realEmbed (entry r j
      (MatrixPhysicalColumnMap.restriction (cellSet (p.length+1) (bottomLeaf p true))
        (measurableSet_cellSet _ _) v.val)))‖ = _
  rw [MatrixCellEntries.restricted_entry, MatrixCellEntries.restricted_entry]
  rfl

/-- Matrix negative localization is a finite sum of the existing
scalar fractional Hardy localization theorem. Constants are uniform
in the mass parameter and dyadic generation. -/
theorem exists_generation {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (hΛ : 1 ≤ Λ) (n : ℕ) (v : Domain (d := d)),
      (∑ x : Grid n, localNorm (leafPath n x) Λ ρ hΛ hρ.le v ^ 2) ≤ C * energy Λ ρ v := by
  obtain ⟨C,hC,hScalar⟩ := SHE.FiniteHaar.exists_sum_localNegativeNorm_bound hρ hρhalf
  let D := (Fintype.card d : ℝ) ^ 2
  refine ⟨1 + D*C, by dsimp [D]; positivity, ?_⟩
  intro Λ hΛ n v
  let f := fun p : List Bool => fun q : d × d =>
    SHE.FiniteHaar.localNegativeNorm p Λ ρ hΛ hρ.le (realEmbed (entry q.1 q.2 v.val))
  have hLocal (p : List Bool) : localNorm p Λ ρ hΛ hρ.le v ^ 2 ≤
      D * ∑ r : d, ∑ j : d, f p (r,j) ^ 2 := by
    rw [localNorm_entries]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (d × d)) (fun _ => (1 : ℝ)) (f p)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, D, pow_two, f] using hh
  calc
    _ ≤ ∑ x : Grid n, D * ∑ r : d, ∑ j : d, f (leafPath n x) (r,j) ^ 2 :=
      Finset.sum_le_sum (fun x _ => hLocal _)
    _ = D * ∑ r : d, ∑ j : d, ∑ x : Grid n, f (leafPath n x) (r,j) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ ≤ D * ∑ r : d, ∑ j : d, C * StepInput.negativeEnergy 1 Λ ρ (realEmbed (entry r j v.val)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [D]; positivity)
      exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => hScalar Λ hΛ n _))
    _ = D*C*energy Λ ρ v := by simp only [energy, Finset.mul_sum, mul_assoc]
    _ ≤ (1 + D*C)*energy Λ ρ v :=
      mul_le_mul_of_nonneg_right (by linarith) (energy_nonneg hΛ v)

end SHEStochastic.MatrixNegativeLocalization
