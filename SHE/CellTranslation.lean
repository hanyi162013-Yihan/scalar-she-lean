module

public import SHE.HaarNegativeColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.CellTranslation
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FiniteHaar ArcFourier
open scoped ENNReal
local instance cellTranslation_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def flag (n : ℕ) (x : Grid n) : AddCircle (1:ℝ) → ℂ := (cellSet n x).indicator (fun _ => (1:ℂ))
def cut (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) : AddCircle (1:ℝ) → ℂ := (cellSet n x).indicator u

theorem flag_memLp (n : ℕ) (x : Grid n) : MemLp (flag n x) 2 haarAddCircle :=
  (memLp_congr_ae (cellIndicator_ae n x)).mp (Lp.memLp (cellIndicator n x))

theorem flag_square (n : ℕ) (x : Grid n) : (∫ y, ‖flag n x y‖^2 ∂haarAddCircle) = (((2^n:ℕ):ℝ))⁻¹ := by
  rw [← cellIndicator_norm_sq,StoppedFourier.L2_norm_sq_eq_integral]
  exact integral_congr_ae ((cellIndicator_ae n x).fun_comp (fun z : ℂ => ‖z‖^2)).symm

theorem flag_translation_bound (n : ℕ) (x : Grid n) {z : ℝ} (hz : 0 ≤ z) :
    circleTranslationEnergy (flag n x) z ≤ 4*min 1 ((((2^n:ℕ):ℝ))*z)*(((2^n:ℕ):ℝ))⁻¹ := by
  let v : ZMod (2^n) → ℝ := fun j => (Pi.single x 1 : Grid n → ℝ) ((gridCellEquiv n).symm j)
  have he : stepLp (2^n) v = cellIndicator n x := rfl
  have hae : CircleStep.circleStep (2^n) v =ᵐ[haarAddCircle] flag n x :=
    (stepLp_ae (2^n) v).symm.trans (by rw [he]; exact cellIndicator_ae n x)
  rw [← translation_congr hae z,CircleStep.circleStep_translationEnergy (2^n) v hz]
  have hn : 0 < (((2^n:ℕ):ℝ)) := by positivity
  have hh := CyclicStep.stepTranslationSq_le_min hn hz (CircleStep.cyclicSuccessor (2^n)) v
  have hnorm : CyclicStep.stepL2Sq (((2^n:ℕ):ℝ)) v = (((2^n:ℕ):ℝ))⁻¹ := by
    unfold CyclicStep.stepL2Sq FiniteTransport.vectorSq
    rw [← stepLp_norm_sq,he,cellIndicator_norm_sq]
  simpa only [hnorm] using hh

theorem translation_four_bound (f : AddCircle (1:ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle) (z : ℝ) :
    circleTranslationEnergy f z ≤ 4*(∫ x, ‖f x‖^2 ∂haarAddCircle) := by
  have hs := hasSum_translation_energy f hf (z : AddCircle (1:ℝ))
  change (∫ x, ‖f (x+(z : AddCircle (1:ℝ)))-f x‖^2 ∂haarAddCircle) ≤ _
  rw [← hs.tsum_eq,← base_tsum f hf,← tsum_mul_left]
  apply hs.summable.tsum_le_tsum _ ((base_summable f hf).mul_left 4)
  intro k
  have hn : ‖fourier k (z : AddCircle (1:ℝ))-1‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans_eq (by simp only [fourier_apply,Circle.norm_coe,norm_one]; norm_num)
  have hh : ‖fourier k (z : AddCircle (1:ℝ))-1‖^2 ≤ 4 := by nlinarith [norm_nonneg (fourier k (z : AddCircle (1:ℝ))-1)]
  exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)

theorem cut_memLp (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) : MemLp (cut n x u) 2 haarAddCircle :=
  (u.memLp haarAddCircle ℂ).indicator (measurableSet_cellSet n x).nullMeasurableSet

theorem cut_square_bound (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (A : ℝ)
    (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ A) :
    (∫ y, ‖cut n x u y‖^2 ∂haarAddCircle) ≤ A^2*(((2^n:ℕ):ℝ))⁻¹ := by
  rw [← flag_square n x,← integral_const_mul]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm (cut_memLp n x u).aestronglyMeasurable).mp (cut_memLp n x u))
    (((memLp_two_iff_integrable_sq_norm (flag_memLp n x).aestronglyMeasurable).mp (flag_memLp n x)).const_mul _)
  intro y
  change ‖(cellSet n x).indicator u y‖^2 ≤ A^2*‖(cellSet n x).indicator (fun _ => (1:ℂ)) y‖^2
  by_cases hy : y ∈ cellSet n x
  · simp only [Set.indicator_of_mem hy,norm_one,one_pow,mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hu y hy) 2
  · simp only [Set.indicator_of_notMem hy,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero]
    exact le_rfl

theorem cut_difference_pointwise (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (A L : ℝ)
    (_hA : 0 ≤ A) (hL : 0 ≤ L) (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ A)
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ L*dist y w)
    (y : AddCircle (1:ℝ)) {z : ℝ} (hz : 0 ≤ z) :
    ‖cut n x u (y+(z : AddCircle (1:ℝ)))-cut n x u y‖^2 ≤
      L^2*z^2*‖flag n x y‖^2+A^2*‖flag n x (y+(z : AddCircle (1:ℝ)))-flag n x y‖^2 := by
  have hd : dist (y+(z : AddCircle (1:ℝ))) y ≤ z := by
    rw [dist_eq_norm,add_sub_cancel_left]
    exact QuotientAddGroup.norm_mk_le_norm.trans_eq (by rw [Real.norm_eq_abs,abs_of_nonneg hz])
  by_cases hy : y ∈ cellSet n x <;> by_cases hw : y+(z : AddCircle (1:ℝ)) ∈ cellSet n x
  · have hh := (hlip _ hw _ hy).trans (mul_le_mul_of_nonneg_left hd hL)
    simpa only [cut,flag,Set.indicator_of_mem hy,Set.indicator_of_mem hw,norm_one,one_pow,mul_one,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  · have hh := pow_le_pow_left₀ (norm_nonneg _) (hu y hy) 2
    simp only [cut,flag,Set.indicator_of_mem hy,Set.indicator_of_notMem hw,zero_sub,norm_neg,norm_one,one_pow,mul_one] at *
    nlinarith
  · have hh := pow_le_pow_left₀ (norm_nonneg _) (hu (y+(z : AddCircle (1:ℝ))) hw) 2
    simpa only [cut,flag,Set.indicator_of_notMem hy,Set.indicator_of_mem hw,sub_zero,norm_one,one_pow,mul_one,norm_zero,
      zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_add] using hh
  · simp only [cut,flag,Set.indicator_of_notMem hy,Set.indicator_of_notMem hw,sub_self,norm_zero,
      zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero,le_refl]

theorem cut_translation_small_bound (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (A L : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ A)
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ L*dist y w)
    {z : ℝ} (hz : 0 ≤ z) :
    circleTranslationEnergy (cut n x u) z ≤
      L^2*z^2*(((2^n:ℕ):ℝ))⁻¹+A^2*(4*min 1 ((((2^n:ℕ):ℝ))*z)*(((2^n:ℕ):ℝ))⁻¹) := by
  have hf := flag_memLp n x
  have ht := hf.comp_measurePreserving (measurePreserving_add_right haarAddCircle (z : AddCircle (1:ℝ)))
  have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hdi := (memLp_two_iff_integrable_sq_norm (ht.sub hf).aestronglyMeasurable).mp (ht.sub hf)
  have hci := cut_memLp n x u
  have hct := hci.comp_measurePreserving (measurePreserving_add_right haarAddCircle (z : AddCircle (1:ℝ)))
  have hi := integral_mono ((memLp_two_iff_integrable_sq_norm (hct.sub hci).aestronglyMeasurable).mp (hct.sub hci))
    ((hfi.const_mul (L^2*z^2)).add (hdi.const_mul (A^2)))
    (fun y => cut_difference_pointwise n x u A L hA hL hu hlip y hz)
  have hsplit := integral_add (hfi.const_mul (L^2*z^2)) (hdi.const_mul (A^2))
  dsimp only [Pi.add_apply] at hi hsplit
  rw [hsplit,integral_const_mul,integral_const_mul,flag_square] at hi
  have hi' : circleTranslationEnergy (cut n x u) z ≤ L^2*z^2*(((2^n:ℕ):ℝ))⁻¹+
      A^2*circleTranslationEnergy (flag n x) z := by
    simpa only [circleTranslationEnergy,Pi.sub_apply,Function.comp_apply] using! hi
  exact hi'.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (flag_translation_bound n x hz) (sq_nonneg A)))

/-- The entire translation modulus of a smooth function cut to a true
dyadic cell depends only on its amplitude and its Lipschitz constant on
that cell; behavior elsewhere is irrelevant. -/
theorem cut_translation_bound (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (A L : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ A)
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ L*dist y w)
    {z : ℝ} (hz : 0 ≤ z) :
    circleTranslationEnergy (cut n x u) z ≤
      (L^2*(((2^n:ℕ):ℝ))⁻¹^3+4*A^2*(((2^n:ℕ):ℝ))⁻¹)*min 1 ((((2^n:ℕ):ℝ))*z) := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  by_cases hs : N*z ≤ 1
  · have hb := cut_translation_small_bound n x u A L hA hL hu hlip hz
    change _ ≤ L^2*z^2*N⁻¹+A^2*(4*min 1 (N*z)*N⁻¹) at hb
    rw [min_eq_right hs] at hb
    change _ ≤ (L^2*N⁻¹^3+4*A^2*N⁻¹)*min 1 (N*z)
    rw [min_eq_right hs]
    apply hb.trans
    have hzN : z ≤ N⁻¹ := by rw [inv_eq_one_div]; exact (le_div_iff₀ hN).mpr (by nlinarith)
    have hz2 : z^2 ≤ N⁻¹*z := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hz2 (mul_nonneg (sq_nonneg L) (inv_nonneg.mpr hN.le))
    have he : (L^2*N⁻¹^3+4*A^2*N⁻¹)*(N*z) = L^2*N⁻¹*(N⁻¹*z)+A^2*(4*(N*z)*N⁻¹) := by field_simp
    rw [he]
    nlinarith
  · have hb := (translation_four_bound (cut n x u) (cut_memLp n x u) z).trans
      (mul_le_mul_of_nonneg_left (cut_square_bound n x u A hu) (by norm_num : (0:ℝ) ≤ 4))
    change _ ≤ (L^2*N⁻¹^3+4*A^2*N⁻¹)*min 1 (N*z)
    rw [min_eq_left (le_of_not_ge hs)]
    have hn : 0 ≤ L^2*N⁻¹^3 := by positivity
    dsimp only [N] at *
    nlinarith

end SHE.CellTranslation
