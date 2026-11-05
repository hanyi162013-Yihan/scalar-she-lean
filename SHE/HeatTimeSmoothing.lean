module

public import SHE.HeatColumnSemigroup
public import SHE.RealHaarIntegrand

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HeatTimeSmoothing
open MeasureTheory Set CircleHeat FiniteHaar
open scoped ENNReal
local instance heatTimeSmoothing_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem scalar_increment_bounds {frequency τ δ : ℝ} (hfrequency : 0 ≤ frequency) (hτ : 0 < τ) (hδ : 0 ≤ δ) :
    Real.exp (-τ*frequency)*(1-Real.exp (-δ*frequency)) ≤ δ/τ ∧
      Real.exp (-τ*frequency)*(1-Real.exp (-δ*frequency)) ≤ 1 := by
  have hEτ : Real.exp (-τ*frequency) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hEδ : Real.exp (-δ*frequency) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hsmall : 1-Real.exp (-δ*frequency) ≤ δ*frequency := by
    have hh := Real.add_one_le_exp (-δ*frequency)
    linarith
  have hpeak : (τ*frequency)*Real.exp (-τ*frequency) ≤ 1 := by
    have hh := Real.mul_exp_neg_le_exp_neg_one (τ*frequency)
    have he : Real.exp (-1:ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    simpa only [neg_mul] using hh.trans he
  constructor
  · apply (le_div_iff₀ hτ).mpr
    calc
      _ ≤ (δ*frequency)*Real.exp (-τ*frequency)*τ := by
        exact mul_le_mul_of_nonneg_right
          (by nlinarith [mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg (-τ*frequency))]) hτ.le
      _ = δ*((τ*frequency)*Real.exp (-τ*frequency)) := by ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left hpeak hδ
      _ = δ := mul_one δ
  · have hb : 1-Real.exp (-δ*frequency) ≤ 1 := by linarith [Real.exp_nonneg (-δ*frequency)]
    exact (mul_le_mul hEτ hb (sub_nonneg.mpr hEδ) zero_le_one).trans_eq (by norm_num)

theorem heatWeight_increment_norm {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (n : ℤ) :
    ‖heatWeight τ n*(heatWeight δ n-1)‖=
      Real.exp (-τ*(2*Real.pi*(n:ℝ))^2)*(1-Real.exp (-δ*(2*Real.pi*(n:ℝ))^2)) := by
  have he : Real.exp (-δ*(2*Real.pi*(n:ℝ))^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) (sq_nonneg _))
  rw [heatWeight,heatWeight,max_eq_left hτ,max_eq_left hδ,norm_mul]
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_of_nonpos (sub_nonpos.mpr he)]
  ring

theorem heatWeight_increment_bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (n : ℤ) :
    ‖heatWeight τ n*(heatWeight δ n-1)‖ ≤ (δ/τ)^θ := by
  rw [heatWeight_increment_norm hτ.le hδ]
  have hb := scalar_increment_bounds (sq_nonneg (2*Real.pi*(n:ℝ))) hτ hδ
  by_cases hr : δ/τ ≤ 1
  · exact hb.1.trans (Real.self_le_rpow_of_le_one (div_nonneg hδ hτ.le) hr hθ1)
  · exact hb.2.trans (Real.one_le_rpow (le_of_not_ge hr) hθ)

theorem heat_increment_bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (v : CircleL2) :
    ‖heat δ (heat τ v)-heat τ v‖ ≤ (δ/τ)^θ*‖v‖ := by
  let R := (δ/τ)^θ
  have hR : 0 ≤ R := Real.rpow_nonneg (div_nonneg hδ hτ.le) θ
  have hc (n : ℤ) : ‖fourierCoeff (heat δ (heat τ v)-heat τ v) n‖^2 ≤
      R^2*‖fourierCoeff v n‖^2 := by
    have he : fourierCoeff (heat δ (heat τ v)-heat τ v) n=
        (heatWeight τ n*(heatWeight δ n-1))*fourierCoeff v n := by
      rw [← fourierBasis_repr]
      simp only [map_sub,lp.coeFn_sub,Pi.sub_apply,fourierBasis_repr,heat_fourierCoeff]
      ring
    rw [he,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (heatWeight_increment_bound hτ hδ hθ hθ1 n) 2) (sq_nonneg _)
  have hs := (summable_fourier_sq (heat δ (heat τ v)-heat τ v)).tsum_le_tsum hc
    ((summable_fourier_sq v).mul_left (R^2))
  rw [← norm_sq_fourier,tsum_mul_left,← norm_sq_fourier] at hs
  change ‖heat δ (heat τ v)-heat τ v‖ ≤ R*‖v‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

end SHE.HeatTimeSmoothing
