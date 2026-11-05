module

public import SHE.HaarColumnBounds

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar
open Finset MeasureTheory AddCircle CircleHeat
local instance haarCellEnergy_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def cellIndicator (n : ℕ) (x : Grid n) : CircleL2 := gridStep n (Pi.single x 1)

theorem cellIndicator_ae (n : ℕ) (x : Grid n) :
    cellIndicator n x =ᵐ[haarAddCircle] (cellSet n x).indicator (fun _ => (1 : ℂ)) := by
  filter_upwards [gridStep_ae_cellIndex n (Pi.single x 1)] with y hy
  change cellIndicator n x y = _ at hy
  rw [hy]
  by_cases hm : y ∈ cellSet n x
  · have he : (gridCellEquiv n).symm (cellIndex n y) = x := by
      apply (gridCellEquiv n).injective
      exact ((gridCellEquiv n).apply_symm_apply _).trans hm
    simp only [he, Pi.single_eq_same, Complex.ofReal_one, Set.indicator_of_mem hm]
  · have he : (gridCellEquiv n).symm (cellIndex n y) ≠ x := by
      intro h
      apply hm
      change cellIndex n y = gridCellEquiv n x
      rw [← h, Equiv.apply_symm_apply]
    simp only [Pi.single_eq_of_ne he, Complex.ofReal_zero, Set.indicator_of_notMem hm]

theorem cellIndicator_norm_sq (n : ℕ) (x : Grid n) :
    ‖cellIndicator n x‖ ^ 2 = (((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [cellIndicator, gridStep_norm_sq]
  simp only [Pi.single_apply]
  simp

theorem cellIndicator_norm (n : ℕ) (x : Grid n) :
    ‖cellIndicator n x‖ = (Real.sqrt (((2 ^ n : ℕ) : ℝ)))⁻¹ := by
  rw [← Real.sqrt_sq (norm_nonneg _), cellIndicator_norm_sq, Real.sqrt_inv]

theorem cellRestriction_inner (n : ℕ) (x : Grid n) (f g : CircleL2) :
    inner ℂ f (cellRestriction n x g) = inner ℂ (cellRestriction n x f) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellRestriction_ae n x f, cellRestriction_ae n x g] with y hf hg
  rw [hf, hg]
  by_cases hy : y ∈ cellSet n x
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, inner_zero_right, inner_zero_left]

theorem cellRestriction_indicator (n : ℕ) (x : Grid n) :
    cellRestriction n x (cellIndicator n x) = cellIndicator n x := by
  apply Lp.ext
  filter_upwards [cellRestriction_ae n x (cellIndicator n x), cellIndicator_ae n x] with y hr hi
  rw [hr]
  by_cases hy : y ∈ cellSet n x
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, hi, Set.indicator_of_notMem hy]

theorem localAverage_cellRestriction (n : ℕ) (x : Grid n) (h : CircleL2) :
    localAverage n (cellRestriction n x h) x = localAverage n h x := by
  unfold localAverage
  change _ * (inner ℂ (cellIndicator n x) (cellRestriction n x h)).re = _
  rw [cellRestriction_inner, cellRestriction_indicator]
  rfl

theorem localAverage_cell_bound (n : ℕ) (x : Grid n) (h : CircleL2) :
    |localAverage n h x| ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ)) * ‖cellRestriction n x h‖ := by
  rw [← localAverage_cellRestriction n x h]
  unfold localAverage
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]
  have hc := (Complex.abs_re_le_norm (inner ℂ (cellIndicator n x) (cellRestriction n x h))).trans
    (norm_inner_le_norm (cellIndicator n x) (cellRestriction n x h))
  calc
    _ ≤ (((2 ^ n : ℕ) : ℝ)) * (‖cellIndicator n x‖ * ‖cellRestriction n x h‖) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [cellIndicator_norm]
      have hs : Real.sqrt (((2 ^ n : ℕ) : ℝ)) ≠ 0 := by positivity
      have he := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))
      field_simp
      rw [he]

theorem cellRestriction_bounded_norm (n : ℕ) (x : Grid n) (h : CircleL2) (M : ℝ)
    (_hM : 0 ≤ M) (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) :
    ‖cellRestriction n x h‖ ≤ M * (Real.sqrt (((2 ^ n : ℕ) : ℝ)))⁻¹ := by
  rw [← cellIndicator_norm n x]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cellRestriction_ae n x h, cellIndicator_ae n x, hh] with y hr hi hh
  rw [hr, hi]
  by_cases hy : y ∈ cellSet n x
  · simp only [Set.indicator_of_mem hy, norm_one, mul_one]
    exact hh
  · simp only [Set.indicator_of_notMem hy, norm_zero, mul_zero, le_refl]

theorem localAverage_bounded_abs (n : ℕ) (x : Grid n) (h : CircleL2) (M : ℝ)
    (hM : 0 ≤ M) (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) :
    |localAverage n h x| ≤ M := by
  have hb := (localAverage_cell_bound n x h).trans
    (mul_le_mul_of_nonneg_left (cellRestriction_bounded_norm n x h M hM hh) (Real.sqrt_nonneg _))
  exact hb.trans_eq (by
    have hs : Real.sqrt (((2 ^ n : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp)

end SHE.FiniteHaar
