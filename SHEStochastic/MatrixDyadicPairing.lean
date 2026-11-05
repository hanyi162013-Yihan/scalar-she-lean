module

public import SHEStochastic.MatrixDyadicMass
public import SHEStochastic.MatrixFiniteFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixDyadicPairing
open MeasureTheory Matrix SHE SHE.FiniteHaar
open scoped Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def leaf (n : ℕ) (x : AddCircle (1 : ℝ)) : Grid n :=
  (gridCellEquiv n).symm (cellIndex n x)

def cross (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (A B : Grid n → Matrix d d ℝ) (x : AddCircle (1 : ℝ)) : Matrix d d ℝ :=
  (A (leaf n x))ᴴ*κ x*B (leaf n x)

theorem cross_partition (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (A B : Grid n → Matrix d d ℝ) (x : AddCircle (1 : ℝ)) :
    cross n κ A B x=∑ z : Grid n, (cellSet n z).indicator (fun y => (A z)ᴴ*κ y*B z) x := by
  rw [Finset.sum_eq_single (leaf n x)]
  · exact (Set.indicator_of_mem ((cellSet_iff _ _ _).mpr rfl) _).symm
  · intro z hz hne
    exact Set.indicator_of_notMem (fun h => hne ((cellSet_iff _ _ _).mp h).symm) _
  · simp

theorem integrable_cross (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Integrable κ μ) (A B : Grid n → Matrix d d ℝ) : Integrable (cross n κ A B) μ := by
  have he : cross n κ A B=fun x =>
      ∑ z : Grid n, (cellSet n z).indicator (fun y => (A z)ᴴ*κ y*B z) x :=
    funext (cross_partition n κ A B)
  rw [he]
  exact integrable_finsetSum _ (fun z _ =>
    ((hκ.const_mul (A z)ᴴ).mul_const (B z)).indicator (measurableSet_cellSet n z))

/-- Spatial integration of two actual dyadic matrix step functions
uses the integrated covariance mass on each cell, with no lost
normalization or off-diagonal component. -/
theorem integral_cross (n : ℕ) (κ : AddCircle (1 : ℝ) → Matrix d d ℝ)
    (hκ : Integrable κ μ) (A B : Grid n → Matrix d d ℝ) :
    (∫ x, cross n κ A B x ∂μ)=
      MatrixFiniteHaar.weightedGram (MatrixDyadicMass.profile κ n) A B := by
  have he : cross n κ A B=fun x =>
      ∑ z : Grid n, (cellSet n z).indicator (fun y => (A z)ᴴ*κ y*B z) x :=
    funext (cross_partition n κ A B)
  rw [he, integral_finsetSum _ (fun z _ =>
    ((hκ.const_mul (A z)ᴴ).mul_const (B z)).indicator (measurableSet_cellSet n z))]
  apply Finset.sum_congr rfl
  intro z hz
  rw [integral_indicator (measurableSet_cellSet n z)]
  rw [integral_mul_const_of_integrable ((hκ.restrict).const_mul (A z)ᴴ),
    integral_const_mul_of_integrable hκ.restrict]
  rfl

end SHEStochastic.MatrixDyadicPairing
