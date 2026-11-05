module

public import SHE.DyadicLocalization

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.CellNegative
open Finset Set MeasureTheory AddCircle CircleHeat FiniteHaar HeatMarkov NegativeNash HaarWeightedHeat ArcFourier ArcNegative DyadicLocalization
open scoped ENNReal InnerProductSpace
local instance cellNegative_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem normOne_cell_supported (n : ℕ) (x : Grid n) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ cellSet n x → v y = 0) :
    normOne v ≤ (Real.sqrt (((2^n:ℕ):ℝ)))⁻¹*‖v‖ := by
  have hh := integral_norm_mul_norm_le (cellIndicator n x) v
  rw [cellIndicator_norm] at hh
  apply le_trans (le_of_eq ?_) hh
  unfold normOne
  apply integral_congr_ae
  filter_upwards [cellIndicator_ae n x,hv] with y hy hv
  rw [hy]
  by_cases hm : y ∈ cellSet n x
  · rw [Set.indicator_of_mem hm,norm_one,one_mul]
  · rw [Set.indicator_of_notMem hm,norm_zero,zero_mul,hv hm,norm_zero]

theorem energy_mass_le {Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (v : CircleL2) :
    Λ^ρ*energy Λ ρ v ≤ ‖v‖^2 := by
  unfold energy
  rw [← tsum_mul_left,norm_sq_fourier]
  apply Summable.tsum_le_tsum _ ((energy_summable hΛ hρ v).mul_left _) (summable_fourier_sq v)
  intro k
  have hw : Λ^ρ*(Λ+(k:ℝ)^2)^(-ρ) ≤ 1 := by
    rw [Real.rpow_neg (by positivity : 0 ≤ Λ+(k:ℝ)^2)]
    rw [← div_eq_mul_inv]
    apply (div_le_one (Real.rpow_pos_of_pos (by positivity) _)).mpr
    exact Real.rpow_le_rpow hΛ.le (le_add_of_nonneg_right (sq_nonneg _)) hρ
  calc
    _ = (Λ^ρ*(Λ+(k:ℝ)^2)^(-ρ))*‖fourierCoeff v k‖^2 := by ring
    _ ≤ 1*‖fourierCoeff v k‖^2 := mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := one_mul _

theorem energy_mesh_le {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ cellSet n x → v y = 0) :
    (((2^n:ℕ):ℝ))^(2*ρ)*energy Λ ρ v ≤ interpolationConstant ρ*‖v‖^2 := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hn := pow_le_pow_left₀ (normOne_nonneg v) (normOne_cell_supported n x v hv) 2
  have hs : (Real.sqrt N)⁻¹^2 = N⁻¹ := by rw [inv_pow,Real.sq_sqrt hN.le]
  have hn' : normOne v^2 ≤ N⁻¹*‖v‖^2 := by
    dsimp only [N] at hs
    simpa only [mul_pow,hs] using! hn
  have he := energy_square_bounds hΛ hρ hρhalf zero_le_one (inv_nonneg.mpr hN.le)
    (sq_nonneg ‖v‖) v (by simp) hn'
  simp only [Real.one_rpow] at he
  have hscale := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hN.le (2*ρ))
  apply hscale.trans_eq
  rw [Real.inv_rpow hN.le,← Real.rpow_neg hN.le]
  calc
    _ = interpolationConstant ρ*(N^(2*ρ)*N^(-(2*ρ)))*‖v‖^2 := by ring
    _ = _ := by rw [← Real.rpow_add hN]; simp

def scale (Λ ρ : ℝ) (n : ℕ) : ℝ := (Λ+(((2^n:ℕ):ℝ))^2)^(ρ/2)
def cellConstant (ρ : ℝ) : ℝ := Real.sqrt (1+interpolationConstant ρ)

theorem cellConstant_one_le {ρ : ℝ} (hρhalf : ρ < 1/2) : 1 ≤ cellConstant ρ := by
  rw [cellConstant]
  exact (Real.one_le_sqrt).mpr (by linarith [interpolationConstant_nonneg hρhalf])

theorem scaled_bessel_cell_le {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) (v : CircleL2) :
    scale Λ ρ n*‖besselHalf Λ ρ hΛ hρ.le (cellRestriction n x v)‖ ≤
      cellConstant ρ*‖cellRestriction n x v‖ := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  let u := cellRestriction n x v
  have hu : ∀ᵐ y ∂haarAddCircle, y ∉ cellSet n x → u y = 0 := by
    filter_upwards [cellRestriction_ae n x v] with y hy hn
    rw [hy,Set.indicator_of_notMem hn]
  have hm := energy_mass_le hΛ0 hρ.le u
  have hn := energy_mesh_le hΛ hρ hρhalf n x u hu
  have hweight : (Λ+(((2^n:ℕ):ℝ))^2)^ρ ≤ Λ^ρ+(((2^n:ℕ):ℝ))^(2*ρ) := by
    have he := Real.rpow_add_le_add_rpow hΛ0.le (sq_nonneg (((2^n:ℕ):ℝ))) hρ.le (by linarith : ρ ≤ 1)
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (((2^n:ℕ):ℝ)))] at he
    norm_num only [Nat.cast_ofNat] at he
    exact he
  have he0 : 0 ≤ energy Λ ρ u := by unfold energy; positivity
  have hproduct := mul_le_mul_of_nonneg_right hweight he0
  have hs : scale Λ ρ n^2 = (Λ+(((2^n:ℕ):ℝ))^2)^ρ := by
    rw [scale,← Real.rpow_mul_natCast (by positivity : 0 ≤ Λ+(((2^n:ℕ):ℝ))^2)]
    norm_num
  have hC : cellConstant ρ^2 = 1+interpolationConstant ρ := Real.sq_sqrt (by linarith [interpolationConstant_nonneg hρhalf])
  apply (sq_le_sq₀ (by unfold scale; positivity) (by unfold cellConstant; positivity)).mp
  rw [mul_pow,mul_pow,besselHalf_norm_sq,hs,hC]
  change (Λ+(((2^n:ℕ):ℝ))^2)^ρ*energy Λ ρ u ≤ _
  nlinarith

theorem localAverage_negative_bound {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) (v : CircleL2) :
    |localAverage n v x| ≤ Real.sqrt (inverseConstant 1 ρ)*Real.sqrt (((2^n:ℕ):ℝ))*scale Λ ρ n*
      ‖besselHalf Λ ρ hΛ hρ.le (cellRestriction n x v)‖ := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  let u := cellRestriction n x v
  have hs := cellIndicator_positive hΛ0.le hρ hρhalf n x
  have hc := InputProjection.weighted_cauchy fourierBasis (weight Λ ρ)
    (fun k => Real.rpow_pos_of_pos (by positivity : 0 < Λ+(k:ℝ)^2) _) u (cellIndicator n x)
    (by simpa only [fourierBasis_repr] using negative_summable hΛ0 hρ.le u)
    (by simpa only [fourierBasis_repr] using hs.1)
  have he : InputProjection.weightedEnergy fourierBasis (fun k => (weight Λ ρ k)⁻¹) u = energy Λ ρ u := by
    simp only [InputProjection.weightedEnergy,fourierBasis_repr,weight,energy]
    apply tsum_congr
    intro k
    rw [Real.rpow_neg (by positivity : 0 ≤ Λ+(k:ℝ)^2)]
  have hp : InputProjection.weightedEnergy fourierBasis (weight Λ ρ) (cellIndicator n x) = positiveSq Λ ρ (cellIndicator n x) := by
    simp only [InputProjection.weightedEnergy,positiveSq,fourierBasis_repr]
  rw [he,hp] at hc
  have hmul := mul_le_mul_of_nonneg_left hs.2 (by unfold energy; positivity : 0 ≤ energy Λ ρ u)
  have hi : |(inner ℂ (cellIndicator n x) u).re|^2 ≤ ‖inner ℂ u (cellIndicator n x)‖^2 := by
    have hh := Complex.abs_re_le_norm (inner ℂ (cellIndicator n x) u)
    rw [norm_inner_symm] at hh
    exact pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [← localAverage_cellRestriction n x v]
  unfold localAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (((2^n:ℕ):ℝ)))]
  have hN : 0 < (((2^n:ℕ):ℝ)) := by positivity
  have hInv : 0 ≤ inverseConstant 1 ρ := inverseConstant_nonneg zero_le_one hρ hρhalf
  apply (sq_le_sq₀ (by positivity) (by unfold scale; positivity)).mp
  simp only [mul_pow,Real.sq_sqrt hInv,Real.sq_sqrt hN.le,besselHalf_norm_sq]
  have hscale : scale Λ ρ n^2 = (Λ+(((2^n:ℕ):ℝ))^2)^ρ := by
    rw [scale,← Real.rpow_mul_natCast (by positivity : 0 ≤ Λ+(((2^n:ℕ):ℝ))^2)]
    norm_num
  rw [hscale]
  have hh := hi.trans (hc.trans hmul)
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (((2^n:ℕ):ℝ)))
  apply hh'.trans_eq
  field_simp
  ring

end SHE.CellNegative
