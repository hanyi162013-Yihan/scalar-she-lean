module

public import SHE.HaarHigherColumns

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
local instance haarTaylor_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem affine_field_segment_bounds (f h : CircleL2) (m U t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U) :
    ∀ᵐ y ∂haarAddCircle, m ≤ ((f+t•h) y).re ∧ ((f+t•h) y).re ≤ U := by
  filter_upwards [Lp.coeFn_add f (t • h), Lp.coeFn_smul t h, Lp.coeFn_add f h, hf, hfh]
    with y ha htsh hah hf hfh
  rw [hah] at hfh
  simp only [Pi.add_apply, Complex.add_re] at hfh
  rw [ha]
  simp only [Pi.add_apply]
  rw [htsh]
  change m ≤ (f y + (t : ℂ) * h y).re ∧ (f y + (t : ℂ) * h y).re ≤ U
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hfh.1), mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hf.1)]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hfh.2), mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hf.2)]

def columnTaylorRemainder (p : List Bool) (f h : CircleL2) (j : ℕ) : CircleL2 :=
  globalHaarColumn (some p) (f+h) -
    ∑ k ∈ range (j+1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k (globalHaarColumn (some p)) f (fun _ => h)

/-- A uniform local bound for the actual integral Taylor remainder at
every finite order, on the genuine elliptic coefficient segment. -/
theorem columnTaylorRemainder_bound (p : List Bool) (f h : CircleL2)
    (m U M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hfreal : ∀ᵐ y ∂haarAddCircle, (f y).im = 0)
    (hhreal : ∀ᵐ y ∂haarAddCircle, (h y).im = 0)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (f y).re ∧ (f y).re ≤ U)
    (hfh : ∀ᵐ y ∂haarAddCircle, m ≤ ((f+h) y).re ∧ ((f+h) y).re ≤ U)
    (hh : ∀ᵐ y ∂haarAddCircle, ‖h y‖ ≤ M) (j : ℕ) :
    ‖columnTaylorRemainder p f h j‖ ≤ (j.factorial : ℝ)⁻¹ * stateJetBound m U hm (j+1) *
      (Real.sqrt (((2 ^ (p.length+1) : ℕ) : ℝ)) * localRestrictionNorm p h) * M ^ j := by
  let C := stateJetBound m U hm (j+1) *
    (Real.sqrt (((2 ^ (p.length+1) : ℕ) : ℝ)) * localRestrictionNorm p h) * M ^ j
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (stateJetBound_nonneg m U hm _)
    (mul_nonneg (Real.sqrt_nonneg _) (localRestrictionNorm_nonneg p h))) (pow_nonneg hM _)
  have hpos (x : Grid (p.length+1)) : 0 < localAverage (p.length+1) f x :=
    hm.trans_le (localAverage_bounds_ae _ f m U hf x).1
  have hpos' (x : Grid (p.length+1)) : 0 < localAverage (p.length+1) (f+h) x :=
    hm.trans_le (localAverage_bounds_ae _ (f+h) m U hfh x).1
  unfold columnTaylorRemainder
  rw [globalHaarColumn_taylor (some p) f h j hpos hpos', add_sub_cancel_left, norm_smul]
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1, ‖(1-t)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f+t•h) (fun _ => h)‖ ≤ C := by
    intro t ht
    have hti : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨hti.1.le, hti.2⟩
    have hjet := globalHaarColumn_jet_one_slot p (f+t•h) m U hm
      (affine_field_real f h t hfreal hhreal) (affine_field_segment_bounds f h m U t ht' hf hfh)
      j (fun _ => h) (fun _ => M) (fun _ => hM) (fun _ _ => hh)
    have hcard : (univ.erase (0 : Fin (j+1))).card = j := by simp
    simp only [prod_const, hcard] at hjet
    have hp : ‖(1-t)^j‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [ht'.2])]
      exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
    rw [norm_smul]
    exact (mul_le_mul hp hjet (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  have hi : ‖∫ t in (0 : ℝ)..1, (1-t)^j •
      iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (f+t•h) (fun _ => h)‖ ≤ C := by
    simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp only [C]
    ring)

theorem columnTaylorRemainder_supported (p : List Bool) (f h : CircleL2) (j : ℕ)
    (hf : ∀ x, 0 < localAverage (p.length+1) f x) :
    ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → columnTaylorRemainder p f h j y = 0 := by
  have hR : nodeRestriction p (columnTaylorRemainder p f h j) = columnTaylorRemainder p f h j := by
    unfold columnTaylorRemainder
    rw [map_sub, nodeRestriction_globalHaarColumn]
    congr 1
    change ((nodeRestriction p).restrictScalars ℝ) _ = _
    rw [map_sum]
    apply sum_congr rfl
    intro k hk
    rw [map_smul]
    congr 1
    change nodeRestriction p _ = _
    apply Lp.ext
    filter_upwards [nodeRestriction_ae p (iteratedFDeriv ℝ k (globalHaarColumn (some p)) f (fun _ => h)),
      globalHaarColumn_jet_supported p f hf k (fun _ => h)] with y hr hs
    rw [hr]
    by_cases hy : y ∈ nodeCell p
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, hs hy]
  filter_upwards [nodeRestriction_ae p (columnTaylorRemainder p f h j)] with y hy
  intro hn
  rw [← hR, hy, Set.indicator_of_notMem hn]

end SHE.FiniteHaar
