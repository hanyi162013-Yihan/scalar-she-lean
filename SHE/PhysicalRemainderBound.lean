module

public import SHE.PhysicalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Genuine absolute heat domination of an inserted physical word.
This proves cutoff Fubini integrability without a master word estimate. -/
noncomputable section
namespace SHE.PhysicalRemainderBound
open Set MeasureTheory ProbabilityTheory Filter AddCircle StoppedFourier ProfileVariance
open WordRecursion CovarianceMatrix CovarianceEndpoint GaussianItoTest PhysicalIto

abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem row_norm_square_integrable {n : ℕ} (Z : Fin n → Observation) {t : ℝ}
    (hZ : ∀ i, t < (Z i).target) :
    Integrable (fun x : HeatCircle => ‖heatRow Z t x‖^2) haarAddCircle := by
  have hi := integrable_finsetSum Finset.univ (fun i _ => heatRow_square_integrable Z hZ i)
  simpa only [EuclideanSpace.real_norm_sq_eq] using hi

theorem row_norm_square_mass_bound {n : ℕ} (Z : Fin n → Observation) {s t : ℝ}
    (ht : t < s) (hZ : ∀ i, s ≤ (Z i).target) :
    (∫ x : HeatCircle, ‖heatRow Z t x‖^2 ∂haarAddCircle) ≤
      (n : ℝ) * (1 + heatConstant * (s - t)^(-(1 / 2 : ℝ))) := by
  have htarget (i : Fin n) : t < (Z i).target := ht.trans_le (hZ i)
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum Finset.univ (fun i _ => heatRow_square_integrable Z htarget i)]
  calc
    _ ≤ ∑ _i : Fin n, (1 + heatConstant * (s - t)^(-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [heatRow_square_mass Z htarget i]
      apply (circleHeat_norm_sq_bound (sub_pos.mpr (htarget i)) _).trans
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ heatConstant_pos.le
      exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ht) (by linarith [hZ i]) (by norm_num)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem inserted_pointwise_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hB : 0 ≤ B)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) {t : ℝ} (ht : t ∈ Ioo W.left W.right)
    (G : State n → ℝ) (hH : ∀ z, ‖GaussianTaylor.hessian G z‖ ≤ B) (x : HeatCircle) :
    ‖insertion a W.coefficient W.observations t x G
        (observe U X (appendObservation W.observations t x) t)‖ ≤
      ((1 / 2 : ℝ) * (A + W.upper) * B) * ‖heatRow W.observations t x‖^2 := by
  let H := GaussianTaylor.hessian G (observe U X W.observations t)
  let row := heatRow W.observations t x
  have hcoef : |a (X (t, x)) - W.coefficient (t, x)| ≤ A + W.upper :=
    (abs_sub _ _).trans (add_le_add (ha _) (W.bounded t (Ioo_subset_Icc_self ht) x))
  have hb := GaussianTaylor.bilinear_norm_le H row row
  have hb' : ‖H row row‖ ≤ B * ‖row‖ * ‖row‖ :=
    hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _)) (norm_nonneg _))
  rw [insertion_observe]
  change ‖(1 / 2 : ℝ) * (a (X (t, x)) - W.coefficient (t, x)) * H row row‖ ≤ _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Real.norm_eq_abs]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by norm_num : (0 : ℝ) ≤ 1 / 2)) hb'
    (norm_nonneg _) (mul_nonneg (by norm_num) (add_nonneg hA W.upper_nonneg))
  convert hh using 1 <;> ring

theorem inserted_spatial_norm_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hB : 0 ≤ B)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) {t : ℝ} (ht : t ∈ Ioo W.left W.right)
    (G : State n → ℝ) (hH : ∀ z, ‖GaussianTaylor.hessian G z‖ ≤ B) :
    ‖∫ x : HeatCircle, insertion a W.coefficient W.observations t x G
        (observe U X (appendObservation W.observations t x) t) ∂haarAddCircle‖ ≤
      ((1 / 2 : ℝ) * (A + W.upper) * B * n) *
        (1 + heatConstant * (W.right - t)^(-(1 / 2 : ℝ))) := by
  let K : ℝ := (1 / 2 : ℝ) * (A + W.upper) * B
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hA W.upper_nonneg)) hB
  have hi := (row_norm_square_integrable W.observations (fun i => ht.2.trans_le (W.target_after i))).const_mul K
  have hh := norm_integral_le_of_norm_le hi (Eventually.of_forall
    (fun x => inserted_pointwise_bound W hA ha hB U X ht G hH x))
  rw [integral_const_mul] at hh
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (row_norm_square_mass_bound W.observations ht.2 W.target_after) hK
  convert hm using 1 <;> ring

theorem remainder_norm_bound {n : ℕ} (W : EndpointWindow n) {a : ℝ → ℝ}
    {A B : ℝ} (hA : 0 ≤ A) (ha : ∀ z, |a z| ≤ A) (hB : 0 ≤ B)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) :
    ‖wordRemainder W a U X F‖ ≤
      ∫ t in W.left..W.right, ((1 / 2 : ℝ) * (A + W.upper) * B * n) *
        (1 + heatConstant * (W.right - t)^(-(1 / 2 : ℝ))) := by
  apply intervalIntegral.norm_integral_le_of_norm_le W.ordered ?_
    (endpoint_majorant_integrable ((1 / 2 : ℝ) * (A + W.upper) * B * n))
  filter_upwards [volume.ae_ne W.right] with t htr ht
  have htin : t ∈ Ioo W.left W.right := ⟨ht.1, lt_of_le_of_ne ht.2 htr⟩
  exact inserted_spatial_norm_bound W hA ha hB U X htin (backward W F t)
    (fun z => BackwardRegularity.gaussian_state_hessian_bound _ hF hbound hD hDD z)

end SHE.PhysicalRemainderBound
