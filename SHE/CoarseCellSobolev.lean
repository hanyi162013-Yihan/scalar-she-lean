module

public import SHE.HaarRowPacket

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.CoarseCellSobolev
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FiniteHaar CellTranslation SmoothCellSobolev ArcFourier
open scoped ENNReal
local instance coarseCellSobolev_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem translation_cap_gagliardo {ρ C D : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hC : 0 ≤ C) (hD : 0 < D) (f : AddCircle (1:ℝ) → ℂ)
    (hm : Measurable (circleTranslationEnergy f))
    (hb : ∀ z : ℝ, 0 ≤ z → circleTranslationEnergy f z ≤ C*min 1 (D*z)) :
    IntegrableOn (fun z : ℝ => circleTranslationEnergy f z*z^(-1-2*ρ)) (Ioi 0) ∧
      circleFractionalSq ρ f ≤ fractionalConstant ρ*D^(2*ρ)*C := by
  have hi := ((kernel_integrable hD hρ hρhalf).const_mul C).integrableOn (s := Ioi (0:ℝ))
  have hpoint {z : ℝ} (hz : 0 < z) : circleTranslationEnergy f z*z^(-1-2*ρ) ≤ C*kernel D ρ z := by
    rw [kernel_eq hD hz]
    exact (mul_le_mul_of_nonneg_right (hb z hz.le) (Real.rpow_nonneg hz.le _)).trans_eq (by ring)
  have hfinite : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z*z^(-1-2*ρ)) (Ioi 0) := by
    apply hi.mono' (hm.mul (by fun_prop)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have ht0 : 0 ≤ circleTranslationEnergy f z := integral_nonneg (fun _ => sq_nonneg _)
    change ‖circleTranslationEnergy f z*z^(-1-2*ρ)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg ht0 (Real.rpow_nonneg hz.le _))]
    exact hpoint hz
  refine ⟨hfinite,?_⟩
  have hh := integral_mono_ae hfinite hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact hpoint hz)
  have ht := setIntegral_le_integral (s := Ioi (0:ℝ)) ((kernel_integrable hD hρ hρhalf).const_mul C)
    (ae_of_all _ (fun z => mul_nonneg hC (kernel_nonneg hD.le z)))
  change (∫ z : ℝ in Ioi 0, circleTranslationEnergy f z*z^(-1-2*ρ)) ≤ _
  exact (hh.trans ht).trans_eq (by rw [integral_const_mul,kernel_integral hD hρ hρhalf]; ring)

theorem coarse_cut_translation {t : ℝ} (ht : 0 < t) (n : ℕ) (x : Grid n)
    (hcoarse : Real.sqrt t ≤ 2/(((2^n:ℕ):ℝ))) (u : C(AddCircle (1:ℝ),ℂ)) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ 1)
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ (K/Real.sqrt t)*dist y w)
    {z : ℝ} (hz : 0 ≤ z) :
    circleTranslationEnergy (cut n x u) z ≤ (((2^n:ℕ):ℝ))⁻¹*(K^2+8)*min 1 ((Real.sqrt t)⁻¹*z) := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  let r := Real.sqrt t
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 0 < r := Real.sqrt_pos.mpr ht
  have hc : r*N ≤ 2 := (le_div_iff₀ hN).mp hcoarse
  by_cases hs : r⁻¹*z ≤ 1
  · have hzsmall : z ≤ r := by
      have hh := (div_le_one hr).mp (by simpa only [div_eq_mul_inv,mul_comm] using hs)
      exact hh
    have hb := cut_translation_small_bound n x u 1 (K/r) zero_le_one (by positivity) hu hlip hz
    have hmin := min_le_right (1:ℝ) (N*z)
    have hbs : circleTranslationEnergy (cut n x u) z ≤ (K/r)^2*z^2*N⁻¹+4*z := by
      have hh := mul_le_mul_of_nonneg_right hmin (by positivity : 0 ≤ 4*N⁻¹)
      have he : (4*N⁻¹)*(N*z) = 4*z := by field_simp
      dsimp only [N] at hh he
      norm_num only [one_pow,one_mul] at hb
      nlinarith
    change _ ≤ N⁻¹*(K^2+8)*min 1 (r⁻¹*z)
    rw [min_eq_right hs]
    apply hbs.trans
    apply (le_of_mul_le_mul_left _ hr)
    field_simp
    nlinarith [mul_nonneg (sq_nonneg K) (mul_nonneg hz (sub_nonneg.mpr hzsmall)),
      mul_nonneg hz (sub_nonneg.mpr hc)]
  · have hb := (translation_four_bound (cut n x u) (cut_memLp n x u) z).trans
      (mul_le_mul_of_nonneg_left (cut_square_bound n x u 1 hu) (by norm_num : (0:ℝ) ≤ 4))
    change _ ≤ N⁻¹*(K^2+8)*min 1 (r⁻¹*z)
    rw [min_eq_left (le_of_not_ge hs)]
    norm_num only [one_pow,one_mul,mul_one] at hb ⊢
    dsimp only [N] at *
    have hi : 0 ≤ (((2^n:ℕ):ℝ))⁻¹ := inv_nonneg.mpr hN.le
    nlinarith [mul_nonneg (sq_nonneg K) (inv_nonneg.mpr hN.le)]

def coarseConstant (ρ K : ℝ) : ℝ := 1+(unitFractionalMass ρ)⁻¹*fractionalConstant ρ*(K^2+8)

/-- Local positive energy of an actual heat-smoothed bounded test row
at every cell coarser than the heat scale. This is the analytic dual
input for localized L¹ negative smoothing. -/
theorem coarse_cut_massive {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t)
    (n : ℕ) (x : Grid n) (hcoarse : Real.sqrt t ≤ 2/(((2^n:ℕ):ℝ)))
    (u : C(AddCircle (1:ℝ),ℂ)) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ 1)
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ (K/Real.sqrt t)*dist y w) :
    Summable (fun k : ℤ => weight Λ ρ k*‖fourierCoeff (cut n x u) k‖^2) ∧
      positiveSq Λ ρ (cut n x u) ≤ coarseConstant ρ K*(((2^n:ℕ):ℝ))⁻¹*(Λ^ρ+t^(-ρ)) := by
  have hN : 0 < (((2^n:ℕ):ℝ)) := by positivity
  have hΛ0 := zero_lt_one.trans_le hΛ
  have hd : 0 < 1-2*ρ := by linarith
  have hF : 0 ≤ fractionalConstant ρ := by unfold fractionalConstant; positivity
  have hM : 0 ≤ (unitFractionalMass ρ)⁻¹ := inv_nonneg.mpr (unitFractionalMass_pos hρ hρhalf).le
  have hg := translation_cap_gagliardo hρ hρhalf (by positivity : 0 ≤ (((2^n:ℕ):ℝ))⁻¹*(K^2+8))
    (inv_pos.mpr (Real.sqrt_pos.mpr ht)) (cut n x u) (measurable_translation_energy n x u)
    (fun z hz => coarse_cut_translation ht n x hcoarse u K hK hu hlip hz)
  refine ⟨massive_summable_of_gagliardo hΛ0.le hρ hρhalf _ (cut_memLp n x u) hg.1,?_⟩
  have he : ((Real.sqrt t)⁻¹)^(2*ρ) = t^(-ρ) := by
    rw [Real.inv_rpow (Real.sqrt_nonneg _),← Real.rpow_neg (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
      ← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [he] at hg
  have hb := massive_le_base_gagliardo hΛ0.le hρ hρhalf _ (cut_memLp n x u) hg.1
  have hs := cut_square_bound n x u 1 hu
  norm_num only [one_pow,one_mul] at hs
  have hs' := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hΛ0.le ρ)
  have hg' := mul_le_mul_of_nonneg_left hg.2 hM
  unfold coarseConstant
  have hmass := Real.rpow_nonneg hΛ0.le ρ
  have ht0 := Real.rpow_nonneg ht.le (-ρ)
  nlinarith [mul_nonneg (by positivity : 0 ≤ (unitFractionalMass ρ)⁻¹*fractionalConstant ρ*(K^2+8)*(((2^n:ℕ):ℝ))⁻¹) hmass,
    mul_nonneg (inv_nonneg.mpr hN.le) ht0]

end SHE.CoarseCellSobolev
