module

public import SHE.HeatPeriodicBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Energy tails for Gaussian periodization, proved from actual line
integrals and elementary inverse-square domination. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatPeriodicEnergy
open MeasureTheory Set Real SHE.HeatOverlap SHE.HeatPeriodization SHE.HeatPeriodicBounds

theorem integrableOn_inverseSquare_Ioi {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi η) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hη
  convert! h using 1
  funext x
  norm_num [Real.rpow_neg_ofNat]

theorem integral_inverseSquare_Ioi {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ in Ioi η, 1 / x ^ 2) = 1 / η := by
  have h := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hη
  convert! h using 1 <;> norm_num [Real.rpow_neg_ofNat, Real.rpow_neg_one]

def inverseSquareTail (η x : ℝ) : ℝ :=
  {y : ℝ | η < |y|}.indicator (fun y => 1 / y ^ 2) x

theorem inverseSquareTail_nonneg (η x : ℝ) : 0 ≤ inverseSquareTail η x := by
  unfold inverseSquareTail
  apply Set.indicator_nonneg
  intro _ _
  positivity

theorem inverseSquareTail_split {η : ℝ} (hη : 0 < η) :
    inverseSquareTail η = (Iio (-η)).indicator (fun y : ℝ => 1 / y ^ 2) +
      (Ioi η).indicator (fun y : ℝ => 1 / y ^ 2) := by
  funext x
  simp only [inverseSquareTail, Pi.add_apply, Set.indicator_apply, Set.mem_ofPred_eq,
    Set.mem_Iio, Set.mem_Ioi]
  by_cases hx : 0 ≤ x
  · have hn : ¬x < -η := by linarith
    simp only [abs_of_nonneg hx, hn, ite_false, zero_add]
  · have hp : ¬η < x := by linarith
    have he : η < -x ↔ x < -η := by constructor <;> intro h <;> linarith
    simp only [abs_of_neg (lt_of_not_ge hx), hp, he, ite_false, add_zero]

theorem integrable_inverseSquareTail {η : ℝ} (hη : 0 < η) :
    Integrable (inverseSquareTail η) := by
  have hp := integrableOn_inverseSquare_Ioi hη
  have hn : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Iio (-η)) := by
    simpa only [neg_Ioi, one_div_neg, neg_sq] using hp.comp_neg
  rw [inverseSquareTail_split hη]
  exact (hn.integrable_indicator measurableSet_Iio).add
    (hp.integrable_indicator measurableSet_Ioi)

theorem integral_inverseSquareTail {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ, inverseSquareTail η x) = 2 / η := by
  have hp := integrableOn_inverseSquare_Ioi hη
  have hn : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Iio (-η)) := by
    simpa only [neg_Ioi, one_div_neg, neg_sq] using hp.comp_neg
  rw [inverseSquareTail_split hη]
  simp only [Pi.add_apply]
  rw [integral_add
    (hn.integrable_indicator measurableSet_Iio) (hp.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi]
  have hi : (∫ x : ℝ in Iio (-η), 1 / x ^ 2) = 1 / η := by
    have h := integral_comp_neg_Ioi η (fun x : ℝ => 1 / x ^ 2)
    rw [integral_Iic_eq_integral_Iio] at h
    have he : (∫ x : ℝ in Iio (-η), 1 / x ^ 2) = ∫ x : ℝ in Ioi η, 1 / x ^ 2 := by
      simpa only [neg_sq] using h.symm
    exact he.trans (integral_inverseSquare_Ioi hη)
  rw [hi, integral_inverseSquare_Ioi hη]
  ring

theorem integrable_inverseSquareTail_shift {η : ℝ} (hη : 0 < η) (a : ℝ) :
    Integrable (fun x : ℝ => inverseSquareTail η (x - a)) := by
  have h := HeatLine.integrable_affine_iff (inverseSquareTail η) (-a)
    (show (1 : ℝ) ≠ 0 by norm_num)
  simpa only [one_mul, neg_add_eq_sub] using h.mpr (integrable_inverseSquareTail hη)

theorem integral_inverseSquareTail_shift {η : ℝ} (hη : 0 < η) (a : ℝ) :
    (∫ x : ℝ, inverseSquareTail η (x - a)) = 2 / η := by
  have h := HeatLine.integral_affine (inverseSquareTail η) (-a) 1
  simpa only [one_mul, inv_one, abs_one, one_smul, neg_add_eq_sub,
    integral_inverseSquareTail hη] using h

theorem gaussian_tail_integral {t η : ℝ} (ht : 0 < t) (hη : 0 < η) (a : ℝ) :
    (∫ x : ℝ in {y : ℝ | η < |y - a|}, exp (-(x - a) ^ 2 / (4 * t))) ≤ 8 * t / η := by
  let S : Set ℝ := {y : ℝ | η < |y - a|}
  have hS : MeasurableSet S := by dsimp only [S]; measurability
  have hig : Integrable (fun x : ℝ => exp (-(x - a) ^ 2 / (4 * t))) := by
    convert! integrable_shifted_gaussian (show 0 < 1 / (4 * t) by positivity) a using 1
    funext x
    congr 1
    ring
  have him := (integrable_inverseSquareTail_shift hη a).const_mul (4 * t)
  have hb : ∀ x : ℝ,
      S.indicator (fun y => exp (-(y - a) ^ 2 / (4 * t))) x ≤
        4 * t * inverseSquareTail η (x - a) := by
    intro x
    by_cases hx : η < |x - a|
    · have hxn : x - a ≠ 0 := abs_pos.mp (hη.trans hx)
      simp only [Set.indicator_of_mem (show x ∈ S from hx), inverseSquareTail,
        Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_true]
      calc
        _ ≤ 1 / ((x - a) ^ 2 / (4 * t)) := by
          simpa only [neg_div] using exp_neg_le_inverse
            (show 0 < (x - a) ^ 2 / (4 * t) by positivity)
        _ = _ := by field_simp
    · simp only [Set.indicator_of_notMem (show x ∉ S from hx), inverseSquareTail,
        Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_false, mul_zero, le_refl]
  calc
    _ = ∫ x : ℝ, S.indicator (fun y => exp (-(y - a) ^ 2 / (4 * t))) x :=
      (integral_indicator hS).symm
    _ ≤ ∫ x : ℝ, 4 * t * inverseSquareTail η (x - a) :=
      integral_mono (hig.indicator hS) him hb
    _ = _ := by rw [integral_const_mul, integral_inverseSquareTail_shift hη a]; ring

theorem outside_interval_subset_tail {η a : ℝ} (ha : |a| ≤ 1 / 2 - η) :
    (Icc (-1 / 2 : ℝ) (1 / 2))ᶜ ⊆ {x : ℝ | η < |x - a|} := by
  intro x hx
  change η < |x - a|
  by_contra hnot
  have hdist : |x - a| ≤ η := le_of_not_gt hnot
  apply hx
  suffices habs : |x| ≤ 1 / 2 by
    have h := abs_le.mp habs
    exact ⟨by linarith [h.1], h.2⟩
  calc
    |x| = |(x - a) + a| := by congr 1; ring
    _ ≤ |x - a| + |a| := abs_add_le _ _
    _ ≤ 1 / 2 := by linarith

theorem gaussian_outside_interval_integral {t η a : ℝ} (ht : 0 < t) (hη : 0 < η)
    (ha : |a| ≤ 1 / 2 - η) :
    (∫ x : ℝ in (Icc (-1 / 2 : ℝ) (1 / 2))ᶜ,
      (sqrt t)⁻¹ * exp (-(x - a) ^ 2 / (4 * t))) ≤ 8 * sqrt t / η := by
  have hig : Integrable (fun x : ℝ => exp (-(x - a) ^ 2 / (4 * t))) := by
    convert! integrable_shifted_gaussian (show 0 < 1 / (4 * t) by positivity) a using 1
    funext x
    congr 1
    ring
  rw [integral_const_mul]
  calc
    _ ≤ (sqrt t)⁻¹ * ∫ x : ℝ in {y : ℝ | η < |y - a|}, exp (-(x - a) ^ 2 / (4 * t)) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hig.integrableOn (ae_of_all _ (fun _ => (exp_pos _).le))
          (ae_of_all _ (outside_interval_subset_tail ha))) (by positivity)
    _ ≤ (sqrt t)⁻¹ * (8 * t / η) :=
      mul_le_mul_of_nonneg_left (gaussian_tail_integral ht hη a) (by positivity)
    _ = _ := by
      calc
        _ = (8 / η) * (t / sqrt t) := by ring
        _ = _ := by rw [div_sqrt]; ring

theorem integrable_squaredGaussian {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Integrable (fun x : ℝ => (sqrt t)⁻¹ * exp (-(x - a) ^ 2 / (4 * t))) := by
  have h := (integrable_shifted_gaussian (show 0 < 1 / (4 * t) by positivity) a).const_mul
    (sqrt t)⁻¹
  convert! h using 1
  funext x
  congr 2
  ring

theorem finite_heat_envelope_outside_energy {q : ℕ} (t a : Fin q → ℝ) (f : ℝ → ℂ)
    {M η h : ℝ} (hM : 0 ≤ M) (ht : ∀ i, 0 < t i) (hth : ∀ i, t i ≤ h)
    (hη : 0 < η) (ha : ∀ i, |a i| ≤ 1 / 2 - η)
    (hi : Integrable (fun x : ℝ => ‖f x‖ ^ 2))
    (hb : ∀ x, ‖f x‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(x - a i) ^ 2 / (4 * t i))) :
    (∫ x : ℝ in (Icc (-1 / 2 : ℝ) (1 / 2))ᶜ, ‖f x‖ ^ 2) ≤
      M * ((q : ℝ) * 8 * sqrt h / η) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ => integrable_squaredGaussian (ht i) (a i))
  calc
    _ ≤ ∫ x : ℝ in (Icc (-1 / 2 : ℝ) (1 / 2))ᶜ,
        M * ∑ i, (sqrt (t i))⁻¹ * exp (-(x - a i) ^ 2 / (4 * t i)) :=
      integral_mono hi.integrableOn (hsum.const_mul M).integrableOn hb
    _ = M * ∑ i, ∫ x : ℝ in (Icc (-1 / 2 : ℝ) (1 / 2))ᶜ,
        (sqrt (t i))⁻¹ * exp (-(x - a i) ^ 2 / (4 * t i)) := by
      rw [integral_const_mul, integral_finsetSum]
      intro i _
      exact (integrable_squaredGaussian (ht i) (a i)).integrableOn
    _ ≤ M * ∑ i : Fin q, 8 * sqrt h / η := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Finset.sum_le_sum
      intro i _
      exact (gaussian_outside_interval_integral (ht i) hη (ha i)).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (hth i)) (by norm_num)) hη.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem norm_sq_le_periodize_sq_add_error {f : ℝ → ℂ} {x K : ℝ} (_hK : 0 ≤ K)
    (herr : ‖periodize f x - f x‖ ≤ K) :
    ‖f x‖ ^ 2 ≤ 2 * ‖periodize f x‖ ^ 2 + 2 * K ^ 2 := by
  have hnorm : ‖f x‖ ≤ ‖periodize f x‖ + K := by
    calc
      _ = ‖periodize f x - (periodize f x - f x)‖ := by congr 1; abel
      _ ≤ ‖periodize f x‖ + ‖periodize f x - f x‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl herr
  nlinarith [norm_nonneg (f x), norm_nonneg (periodize f x),
    sq_nonneg (‖periodize f x‖ - K)]

theorem finite_heat_periodization_energy_bound {q : ℕ} (t a : Fin q → ℝ) (f : ℝ → ℂ)
    {M η h : ℝ} (hM : 0 ≤ M) (ht : ∀ i, 0 < t i) (hth : ∀ i, t i ≤ h)
    (hh : h ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (ha : ∀ i, |a i| ≤ 1 / 2 - η)
    (hi : Integrable (fun x : ℝ => ‖f x‖ ^ 2))
    (hP : IntegrableOn (fun x : ℝ => ‖periodize f x‖ ^ 2) (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hb : ∀ x, ‖f x‖ ^ 2 ≤ M * ∑ i, (sqrt (t i))⁻¹ * exp (-(x - a i) ^ 2 / (4 * t i))) :
    (∫ x : ℝ, ‖f x‖ ^ 2) ≤
      2 * (∫ x : ℝ in Icc (-1 / 2 : ℝ) (1 / 2), ‖periodize f x‖ ^ 2) +
      M * ((q : ℝ) * 8 * sqrt h / η +
        2 * ((q : ℝ) * (8 / η ^ 2)) ^ 2 * h * inverseSquareSum ^ 2) := by
  let K : ℝ := sqrt M * ((q : ℝ) * (8 / η ^ 2) * sqrt h) * inverseSquareSum
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) inverseSquareSum_nonneg
  have herr : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖periodize f x - f x‖ ≤ K := by
    intro x hx
    apply norm_periodize_sub_finite_heat_uniform t a f hM ht hth hh hη hη1
      (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) ha hb
  have hconst : IntegrableOn (fun _ : ℝ => 2 * K ^ 2) (Icc (-1 / 2 : ℝ) (1 / 2)) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hin : (∫ x : ℝ in Icc (-1 / 2 : ℝ) (1 / 2), ‖f x‖ ^ 2) ≤
      2 * (∫ x : ℝ in Icc (-1 / 2 : ℝ) (1 / 2), ‖periodize f x‖ ^ 2) + 2 * K ^ 2 := by
    calc
      _ ≤ ∫ x : ℝ in Icc (-1 / 2 : ℝ) (1 / 2),
          (2 * ‖periodize f x‖ ^ 2 + 2 * K ^ 2) := by
        apply setIntegral_mono_on hi.integrableOn
          ((hP.const_mul 2).add hconst)
          measurableSet_Icc
        exact fun x hx => norm_sq_le_periodize_sq_add_error hK (herr x hx)
      _ = _ := by
        rw [integral_add (hP.const_mul 2) hconst, integral_const_mul]
        norm_num
  have hout := finite_heat_envelope_outside_energy t a f hM ht hth hη ha hi hb
  have hsplit := integral_add_compl (s := Icc (-1 / 2 : ℝ) (1 / 2)) measurableSet_Icc hi
  have hKs : K ^ 2 = M * ((q : ℝ) * (8 / η ^ 2)) ^ 2 * h * inverseSquareSum ^ 2 := by
    dsimp only [K]
    rw [mul_pow, mul_pow, mul_pow, sq_sqrt hM]
    by_cases hh0 : 0 ≤ h
    · rw [sq_sqrt hh0]
      ring
    · have hq : q = 0 := by
        by_contra hq
        have hp := ht ⟨0, Nat.pos_of_ne_zero hq⟩
        have hu := hth ⟨0, Nat.pos_of_ne_zero hq⟩
        linarith
      norm_num [hq]
  rw [hKs] at hin
  nlinarith

theorem exists_periodization_energy_cutoff (q : ℕ) (C η : ℝ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      C * ((q : ℝ) * 8 * sqrt h / η +
        2 * ((q : ℝ) * (8 / η ^ 2)) ^ 2 * h * inverseSquareSum ^ 2) ≤ 1 / 2 := by
  let F : ℝ → ℝ := fun h => C * ((q : ℝ) * 8 * sqrt h / η +
    2 * ((q : ℝ) * (8 / η ^ 2)) ^ 2 * h * inverseSquareSum ^ 2)
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hlim : Filter.Tendsto F (nhds 0) (nhds 0) := by
    simpa only [F, sqrt_zero, mul_zero, zero_mul, zero_div, add_zero, zero_add] using hF.tendsto 0
  have he : ∀ᶠ h in nhds (0 : ℝ), F h < 1 / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min 1 (δ / 2), lt_min zero_lt_one (by positivity), min_le_left _ _, ?_⟩
  intro h hh hhδ
  have hdist : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh]
    have := hhδ.trans (min_le_right 1 (δ / 2))
    linarith
  exact (hnear hdist).le

theorem finite_heat_periodization_energy_comparison {q : ℕ}
    (t a : Fin q → ℝ) (f : ℝ → ℂ) {C η h : ℝ}
    (hC : 0 ≤ C) (ht : ∀ i, 0 < t i) (hth : ∀ i, t i ≤ h)
    (hh : h ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (ha : ∀ i, |a i| ≤ 1 / 2 - η)
    (hi : Integrable (fun x : ℝ => ‖f x‖ ^ 2))
    (hP : IntegrableOn (fun x : ℝ => ‖periodize f x‖ ^ 2) (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hsmall : C * ((q : ℝ) * 8 * sqrt h / η +
      2 * ((q : ℝ) * (8 / η ^ 2)) ^ 2 * h * inverseSquareSum ^ 2) ≤ 1 / 2)
    (hb : ∀ x, ‖f x‖ ^ 2 ≤ C * (∫ y : ℝ, ‖f y‖ ^ 2) *
      ∑ i, (sqrt (t i))⁻¹ * exp (-(x - a i) ^ 2 / (4 * t i))) :
    (∫ x : ℝ, ‖f x‖ ^ 2) ≤
      4 * (∫ x : ℝ in Icc (-1 / 2 : ℝ) (1 / 2), ‖periodize f x‖ ^ 2) := by
  have hE : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hbnd := finite_heat_periodization_energy_bound t a f (mul_nonneg hC hE)
    ht hth hh hη hη1 ha hi hP hb
  have hs := mul_le_mul_of_nonneg_right hsmall hE
  nlinarith

end SHE.HeatPeriodicEnergy
