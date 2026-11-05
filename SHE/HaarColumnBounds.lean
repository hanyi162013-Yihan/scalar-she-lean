module

public import SHE.HaarLocalColumns

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE

theorem haar_child_abs_bound {m l r : ℝ} (hm : 0 < m) (hl : m ≤ l) (hr : m ≤ r) :
    |haarLeft l r| ≤ (Real.sqrt m)⁻¹ ∧ |haarRight l r| ≤ (Real.sqrt m)⁻¹ := by
  have hlp := hm.trans_le hl
  have hrp := hm.trans_le hr
  have hn := haar_normalization hlp hrp
  have hL : (haarLeft l r) ^ 2 ≤ m⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hm).mpr
    nlinarith [mul_nonneg hrp.le (sq_nonneg (haarRight l r)), mul_le_mul_of_nonneg_right hl (sq_nonneg (haarLeft l r))]
  have hR : (haarRight l r) ^ 2 ≤ m⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hm).mpr
    nlinarith [mul_nonneg hlp.le (sq_nonneg (haarLeft l r)), mul_le_mul_of_nonneg_right hr (sq_nonneg (haarRight l r))]
  constructor
  · simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_inv] using Real.sqrt_le_sqrt hL
  · simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_inv] using Real.sqrt_le_sqrt hR

theorem normalized_mass_difference_bound {m l r : ℝ} (hm : 0 < m) (hl : m ≤ l) (hr : m ≤ r)
    (L R : ℝ) : |R / r - L / l - (L + R) / (l + r)| ≤ 2 / m * (|L| + |R|) := by
  have hlp := hm.trans_le hl
  have hrp := hm.trans_le hr
  have hsum : m ≤ l + r := hl.trans (le_add_of_nonneg_right hrp.le)
  calc
    _ ≤ |R / r| + |L / l| + |(L + R) / (l + r)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ = |R| / r + |L| / l + |L + R| / (l + r) := by
      simp only [abs_div, abs_of_pos hlp, abs_of_pos hrp, abs_of_pos (add_pos hlp hrp)]
    _ ≤ |R| / m + |L| / m + (|L| + |R|) / m := by
      exact add_le_add
        (add_le_add (div_le_div_of_nonneg_left (abs_nonneg R) hm hr)
          (div_le_div_of_nonneg_left (abs_nonneg L) hm hl))
        ((div_le_div_of_nonneg_right (abs_add_le L R) (add_pos hlp hrp).le).trans
          (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) hm hsum))
    _ = _ := by ring

theorem haar_child_differential_abs_bound {m l r : ℝ} (hm : 0 < m) (hl : m ≤ l) (hr : m ≤ r)
    (L R : ℝ) :
    |haarLeftDifferential l r L R| ≤ (Real.sqrt m)⁻¹ / m * (|L| + |R|) ∧
      |haarRightDifferential l r L R| ≤ (Real.sqrt m)⁻¹ / m * (|L| + |R|) := by
  have hc := haar_child_abs_bound hm hl hr
  constructor
  · unfold haarLeftDifferential
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ ((Real.sqrt m)⁻¹ / 2) * (2 / m * (|L| + |R|)) :=
        mul_le_mul (div_le_div_of_nonneg_right hc.1 (by norm_num))
          (normalized_mass_difference_bound hm hl hr L R) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold haarRightDifferential
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hd : |L / l - R / r - (L + R) / (l + r)| ≤ 2 / m * (|L| + |R|) := by
      simpa only [add_comm] using normalized_mass_difference_bound hm hr hl R L
    calc
      _ ≤ ((Real.sqrt m)⁻¹ / 2) * (2 / m * (|L| + |R|)) :=
        mul_le_mul (div_le_div_of_nonneg_right hc.2 (by norm_num)) hd (abs_nonneg _) (by positivity)
      _ = _ := by ring

namespace FiniteHaar
open MeasureTheory AddCircle CircleHeat
local instance haarColumnBounds_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem childCoefficient_bound (p : List Bool) (f : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (b : Bool) :
    |childCoefficient p f b| ≤ (Real.sqrt m)⁻¹ := by
  have h := haar_child_abs_bound hm
    (localAverage_bounds_ae _ f m U hf (bottomLeaf p false)).1
    (localAverage_bounds_ae _ f m U hf (bottomLeaf p true)).1
  cases b
  · exact h.1
  · exact h.2

def localDirectionMass (p : List Bool) (h : CircleL2) : ℝ :=
  |localAverage (p.length + 1) h (bottomLeaf p false)| +
    |localAverage (p.length + 1) h (bottomLeaf p true)|

theorem localDirectionMass_nonneg (p : List Bool) (h : CircleL2) : 0 ≤ localDirectionMass p h :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem childDifferential_bound (p : List Bool) (f h : CircleL2) (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (b : Bool) :
    |childDifferential p f h b| ≤ (Real.sqrt m)⁻¹ / m * localDirectionMass p h := by
  have h := haar_child_differential_abs_bound hm
    (localAverage_bounds_ae _ f m U hf (bottomLeaf p false)).1
    (localAverage_bounds_ae _ f m U hf (bottomLeaf p true)).1
    (localAverage (p.length + 1) h (bottomLeaf p false))
    (localAverage (p.length + 1) h (bottomLeaf p true))
  cases b
  · exact h.1
  · exact h.2

theorem cellSet_disjoint (n : ℕ) (x z : Grid n) (hxz : x ≠ z) : Disjoint (cellSet n x) (cellSet n z) := by
  apply Set.disjoint_left.mpr
  intro y hx hz
  apply hxz
  apply (gridCellEquiv n).injective
  exact hx.symm.trans hz

def columnPointBound (p : List Bool) (h : CircleL2) (m U : ℝ) (y : AddCircle (1 : ℝ)) : ℝ :=
  Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * (Real.sqrt m)⁻¹ *
    (‖h y‖ + U / m * localDirectionMass p h)

theorem childDerivativeTerm_pointwise_bound (p : List Bool) (f h : CircleL2) (m U : ℝ)
    (hm : 0 < m) (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) (b : Bool) :
    ∀ᵐ y ∂haarAddCircle, ‖childDerivativeTerm p f h b y‖ ≤
      (cellSet (p.length + 1) (bottomLeaf p b)).indicator (columnPointBound p h m U) y := by
  have hU := elliptic_upper_nonneg f m U hm hf
  have hc := childCoefficient_bound p f m U hm hf b
  have hd := childDifferential_bound p f h m U hm hf b
  filter_upwards [childDerivativeTerm_ae p f h b,
    CircleMultiplier.elliptic_norm_bound f m U hm hfreal hf] with y hy hfy
  rw [hy]
  by_cases hym : y ∈ cellSet (p.length + 1) (bottomLeaf p b)
  · rw [Set.indicator_of_mem hym, Set.indicator_of_mem hym]
    calc
      _ ≤ ‖(Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childDifferential p f h b : ℝ) • f y‖ +
          ‖(Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * childCoefficient p f b : ℝ) • h y‖ := norm_add_le _ _
      _ = Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * |childDifferential p f h b| * ‖f y‖ +
          Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * |childCoefficient p f b| * ‖h y‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * ((Real.sqrt m)⁻¹ / m * localDirectionMass p h) * U +
          Real.sqrt (((2 ^ (p.length + 1) : ℕ) : ℝ)) * (Real.sqrt m)⁻¹ * ‖h y‖ := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)) hfy (norm_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (localDirectionMass_nonneg p h)))
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)) (norm_nonneg _)
      _ = _ := by unfold columnPointBound; ring
  · simp only [Set.indicator_of_notMem hym, norm_zero, le_refl]

/-- The actual first-derivative one-slot bound: one local unaveraged
direction and its two true child averages, supported on the node.
The factor `sqrt(2^(depth))` is proportional to `|I|^(-1/2)`. -/
theorem columnDifferential_pointwise_bound (p : List Bool) (f h : CircleL2) (m U : ℝ)
    (hm : 0 < m) (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, ‖columnDifferential (some p) f h y‖ ≤
      (nodeCell p).indicator (columnPointBound p h m U) y := by
  have hpos (x : Grid (p.length + 1)) : 0 < localAverage (p.length + 1) f x :=
    hm.trans_le (localAverage_bounds_ae _ f m U hf x).1
  rw [columnDifferential_two_children p f h hpos]
  filter_upwards [Lp.coeFn_add (childDerivativeTerm p f h false) (childDerivativeTerm p f h true),
    childDerivativeTerm_pointwise_bound p f h m U hm hfreal hf false,
    childDerivativeTerm_pointwise_bound p f h m U hm hfreal hf true] with y ha hl hr
  rw [ha]
  simp only [Pi.add_apply]
  have hb := (norm_add_le (childDerivativeTerm p f h false y) (childDerivativeTerm p f h true y)).trans
    (add_le_add hl hr)
  have hd := Set.disjoint_left.mp (cellSet_disjoint (p.length+1) _ _ (bottomLeaf_ne p))
  by_cases hyl : y ∈ cellSet (p.length + 1) (bottomLeaf p false)
  · have hyr : y ∉ cellSet (p.length + 1) (bottomLeaf p true) := fun hy => hd hyl hy
    simpa only [Set.indicator_of_mem hyl, Set.indicator_of_notMem hyr,
      Set.indicator_of_mem (show y ∈ nodeCell p from Or.inl hyl), add_zero] using hb
  · by_cases hyr : y ∈ cellSet (p.length + 1) (bottomLeaf p true)
    · simpa only [Set.indicator_of_notMem hyl, Set.indicator_of_mem hyr,
        Set.indicator_of_mem (show y ∈ nodeCell p from Or.inr hyr), zero_add] using hb
    · simpa only [Set.indicator_of_notMem hyl, Set.indicator_of_notMem hyr,
        Set.indicator_of_notMem (show y ∉ nodeCell p from fun hy => hy.elim hyl hyr), add_zero] using hb

end FiniteHaar
end SHE
