module

public import SHE.HeatTimeSmoothing
public import SHE.HaarIntegrandEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.HaarKernelTimeIncrement
open MeasureTheory Set CircleHeat FiniteHaar HeatColumnSemigroup
open scoped ENNReal
local instance haarKernelTimeIncrement_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem column_increment_bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (v : HaarHeatIntegrand.Columns) :
    ‖operator δ (operator τ v)-operator τ v‖ ≤ (δ/τ)^θ*‖v‖ := by
  let L : CircleL2 →L[ℂ] CircleL2 :=
    ((heat δ)-ContinuousLinearMap.id ℂ CircleL2).comp (heat τ)
  have hR : 0 ≤ (δ/τ)^θ := Real.rpow_nonneg (div_nonneg hδ hτ.le) θ
  have hL : ‖L‖ ≤ (δ/τ)^θ := ContinuousLinearMap.opNorm_le_bound _ hR (fun w => by
    exact HeatTimeSmoothing.heat_increment_bound hτ hδ hθ hθ1 w)
  have he : operator δ (operator τ v)-operator τ v=HilbertColumns.mapCLM L v := by
    apply lp.ext
    funext q
    rfl
  rw [he]
  exact (HilbertColumns.map_norm_le L v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- A quantitative time increment in the genuine countable Hilbert--
Schmidt column norm. The coefficient field is the literal common-Haar
factor and may be merely bounded measurable in physical space. -/
theorem complex_kernel_increment_bound {ell M τ δ θ : ℝ} (hell : 0 < ell)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : EllipticField ell M) :
    ‖HaarHeatIntegrand.kernel ell M hell (τ+δ,f)-HaarHeatIntegrand.kernel ell M hell (τ,f)‖ ≤
      (δ/(τ/2))^θ*‖HaarHeatIntegrand.kernel ell M hell (τ/2,f)‖ := by
  have hh : 0 < τ/2 := by positivity
  have hsplit : HaarHeatIntegrand.kernel ell M hell (τ,f)=
      operator (τ/2) (HaarHeatIntegrand.kernel ell M hell (τ/2,f)) := by
    simpa only [show τ/2+τ/2=τ by ring] using kernel_forward hell hh hh.le f
  rw [kernel_forward hell hτ hδ,hsplit]
  exact column_increment_bound hh hδ hθ hθ1 _

theorem real_kernel_increment_sq {ell M τ δ θ : ℝ} (hell : 0 < ell)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : EllipticField ell M) :
    ‖RealHaarIntegrand.kernel ell M hell (τ+δ,f)-RealHaarIntegrand.kernel ell M hell (τ,f)‖^2 ≤
      ((δ/(τ/2))^θ)^2*(HaarIntegrandEnergy.singleConstant M*(τ/2)^(-(1/2:ℝ))) := by
  rw [RealHaarIntegrand.kernel_difference_norm_sq]
  have hb := pow_le_pow_left₀ (norm_nonneg _) (complex_kernel_increment_bound hell hτ hδ hθ hθ1 f) 2
  rw [mul_pow] at hb
  have hhalf : τ/2 ≤ 1 := by linarith
  have hK := HaarIntegrandEnergy.kernel_small_bound hell (by positivity : 0 < τ/2) hhalf f
  rw [RealHaarIntegrand.kernel_norm_sq] at hK
  exact hb.trans (mul_le_mul_of_nonneg_left hK (sq_nonneg _))

/-- A fixed integrable rate sufficient for continuous-version estimates:
the old-noise squared increment is bounded by δ^(1/4) τ^(-3/4). -/
theorem real_kernel_increment_rate {ell M τ δ : ℝ} (hell : 0 < ell)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ) (f : EllipticField ell M) :
    ‖RealHaarIntegrand.kernel ell M hell (τ+δ,f)-RealHaarIntegrand.kernel ell M hell (τ,f)‖^2 ≤
      ((2:ℝ)^(3/4:ℝ)*HaarIntegrandEnergy.singleConstant M)*δ^(1/4:ℝ)*τ^(-(3/4:ℝ)) := by
  have hb := real_kernel_increment_sq (θ := 1/8) hell hτ hτ1 hδ (by norm_num) (by norm_num) f
  have hh : 0 < τ/2 := by positivity
  have he : ((δ/(τ/2))^(1/8:ℝ))^2*(HaarIntegrandEnergy.singleConstant M*(τ/2)^(-(1/2:ℝ)))=
      ((2:ℝ)^(3/4:ℝ)*HaarIntegrandEnergy.singleConstant M)*δ^(1/4:ℝ)*τ^(-(3/4:ℝ)) := by
    rw [← Real.rpow_mul_natCast (div_nonneg hδ hh.le)]
    norm_num only [Nat.cast_ofNat,show (1/8:ℝ)*2=1/4 by norm_num]
    rw [Real.div_rpow hδ hh.le,div_eq_mul_inv,← Real.rpow_neg hh.le]
    calc
      _ = HaarIntegrandEnergy.singleConstant M*δ^(1/4:ℝ)*
          ((τ/2)^(-(1/4:ℝ))*(τ/2)^(-(1/2:ℝ))) := by ring
      _ = HaarIntegrandEnergy.singleConstant M*δ^(1/4:ℝ)*(τ/2)^(-(3/4:ℝ)) := by
        rw [← Real.rpow_add hh]
        norm_num
      _ = _ := by
        rw [Real.div_rpow hτ.le (by norm_num : (0:ℝ) ≤ 2)]
        simp only [div_eq_mul_inv]
        rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        norm_num only [neg_neg]
        ring
  rw [he] at hb
  exact hb

end SHE.HaarKernelTimeIncrement
