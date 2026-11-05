module

public import SHEStochastic.MatrixGlobalHaar
public import SHEStochastic.DyadicCellRefinement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixDyadicMass
open MeasureTheory SHE SHE.FiniteHaar MatrixHaarFunctions
open scoped MatrixOrder Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- The finite matrix data are the actual integrated covariance
profile on the existing periodic dyadic cells. -/
def profile (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (n : ℕ) (i : Grid n) : Matrix d d ℝ :=
  mass μ κ (cellSet n i)

theorem total (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ) (n : ℕ) :
    MatrixFiniteHaar.totalMass n (profile κ n) = ∫ x, κ x ∂μ :=
  (DyadicCellRefinement.integral_partition n κ hκ).symm

theorem refine (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (n r : ℕ) (i : Grid n) :
    profile κ n i = ∑ z : Grid (n+r), if ancestorLeaf n r z=i then profile κ (n+r) z else 0 :=
  DyadicCellRefinement.integral n r i κ hκ

/-- Exact interval-length ellipticity for the actual finite profiles. -/
theorem lower (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (m : ℝ) (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x) (n : ℕ) (i : Grid n) :
    ((((2^n : ℕ) : ℝ))⁻¹*m) • (1 : Matrix d d ℝ) ≤ profile κ n i := by
  have hh := MatrixHaarMass.lower μ κ hκ m hLo (cellSet n i)
  rwa [DyadicCellRefinement.measure_real] at hh

theorem upper (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (U : ℝ) (hHi : ∀ᵐ x ∂μ, κ x ≤ U • (1 : Matrix d d ℝ)) (n : ℕ) (i : Grid n) :
    profile κ n i ≤ ((((2^n : ℕ) : ℝ))⁻¹*U) • (1 : Matrix d d ℝ) := by
  have hh := MatrixHaarMass.upper μ κ hκ U hHi (cellSet n i)
  rwa [DyadicCellRefinement.measure_real] at hh

theorem positive (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (n : ℕ) (i : Grid n) : (profile κ n i).PosDef :=
  MatrixHaarMass.posDef μ κ hκ m hm hLo _ (MatrixGlobalHaar.cell_positive n i)


/-- Literal matrix-valued dyadic averaging: integrated cell mass divided
by the exact cell length. -/
def average (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (n : ℕ) (i : Grid n) : Matrix d d ℝ :=
  (((2^n : ℕ) : ℝ)) • profile κ n i

theorem average_lower (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (m : ℝ) (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x) (n : ℕ) (i : Grid n) :
    m • (1 : Matrix d d ℝ) ≤ average κ n i := by
  have hn : (((2^n : ℕ) : ℝ))≠0 := by positivity
  have hh := smul_le_smul_of_nonneg_left (lower κ hκ m hLo n i)
    (by positivity : 0≤(((2^n : ℕ) : ℝ)))
  simpa only [average, smul_smul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul] using hh

theorem average_upper (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (U : ℝ) (hHi : ∀ᵐ x ∂μ, κ x ≤ U • (1 : Matrix d d ℝ)) (n : ℕ) (i : Grid n) :
    average κ n i ≤ U • (1 : Matrix d d ℝ) := by
  have hn : (((2^n : ℕ) : ℝ))≠0 := by positivity
  have hh := smul_le_smul_of_nonneg_left (upper κ hκ U hHi n i)
    (by positivity : 0≤(((2^n : ℕ) : ℝ)))
  simpa only [average, smul_smul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul] using hh


theorem average_positive (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ᵐ x ∂μ, m • (1 : Matrix d d ℝ) ≤ κ x)
    (n : ℕ) (i : Grid n) : (average κ n i).PosDef :=
  (positive κ hκ m hm hLo n i).smul (by positivity)

/-- Exact coarsening of normalized matrix averages, with the actual
number `2^r` of descendant cells. -/
theorem average_refine (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ)
    (n r : ℕ) (i : Grid n) :
    average κ n i = (((2^r : ℕ) : ℝ))⁻¹ •
      ∑ z : Grid (n+r), if ancestorLeaf n r z=i then average κ (n+r) z else 0 := by
  have he : (∑ z : Grid (n+r), if ancestorLeaf n r z=i then average κ (n+r) z else 0)=
      (((2^(n+r) : ℕ) : ℝ)) • ∑ z : Grid (n+r),
        if ancestorLeaf n r z=i then profile κ (n+r) z else 0 := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases ha : ancestorLeaf n r z=i <;> simp [ha, average]
  have hc : (((2^r : ℕ) : ℝ))⁻¹*(((2^(n+r) : ℕ) : ℝ))=(((2^n : ℕ) : ℝ)) := by
    rw [Nat.pow_add, Nat.cast_mul]
    field_simp <;> ring
  rw [he, smul_smul, hc, ← refine κ hκ n r i]
  rfl


/-- Total normalized finite covariance keeps the exact grid-size
factor relative to the actual spatial covariance integral. -/
theorem total_average (κ : AddCircle (1 : ℝ) → Matrix d d ℝ) (hκ : Integrable κ μ) (n : ℕ) :
    MatrixFiniteHaar.totalMass n (average κ n)=(((2^n : ℕ) : ℝ)) • (∫ x, κ x ∂μ) := by
  simpa only [MatrixFiniteHaar.totalMass, average, Finset.smul_sum] using
    congrArg (fun A : Matrix d d ℝ => (((2^n : ℕ) : ℝ)) • A) (total κ hκ n)

end SHEStochastic.MatrixDyadicMass
