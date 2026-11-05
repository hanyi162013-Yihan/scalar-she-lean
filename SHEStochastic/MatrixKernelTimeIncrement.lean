module

public import SHEStochastic.VectorHeatTimeSmoothing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixKernelTimeIncrement
open MeasureTheory SHE MatrixInfiniteHaar MatrixAnalyticKernel NativeHeatObservation
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Quantitative time smoothing in the actual infinite matrix Haar
column space, with the paper's analytic heat clock. -/
theorem bound {τ δ θ : ℝ} (hτ : 0 < τ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (P : Profile d) :
    ‖kernel (τ+δ) P-kernel τ P‖ ≤ (δ/(τ/2))^θ*‖kernel (τ/2) P‖ := by
  have hh : 0 < τ/2 := by positivity
  have hs : kernel τ P=MatrixHeatColumnFlow.operator ((τ/2)/timeScale) (kernel (τ/2) P) := by
    simpa only [show τ/2+τ/2=τ by ring] using MatrixHeatColumnFlow.analytic_forward hh hh.le P
  rw [MatrixHeatColumnFlow.analytic_forward hτ hδ,hs]
  have hb := VectorHeatTimeSmoothing.columns_bound (div_pos hh timeScale_pos)
    (div_nonneg hδ timeScale_pos.le) hθ hθ1 (kernel (τ/2) P)
  have he : (δ/timeScale)/((τ/2)/timeScale)=δ/(τ/2) := by
    field_simp [timeScale_pos.ne']
  rwa [he] at hb

theorem square_bound {τ δ θ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (P : Profile d) :
    ‖kernel (τ+δ) P-kernel τ P‖^2 ≤
      ((δ/(τ/2))^θ)^2*(constant d P.upper*(τ/2)^(-(1/2 : ℝ))) := by
  have hb := pow_le_pow_left₀ (norm_nonneg _) (bound hτ hδ hθ hθ1 P) 2
  rw [mul_pow] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (small_bound (by positivity : 0 < τ/2) (by linarith : τ/2 ≤ 1) P) (sq_nonneg _))

def constant (d : Type*) [Fintype d] (U : ℝ) : ℝ :=
  (2 : ℝ)^(3/4 : ℝ)*MatrixAnalyticKernel.constant d U

theorem constant_nonneg {U : ℝ} (hU : 0 ≤ U) : 0 ≤ constant d U :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (MatrixAnalyticKernel.constant_nonneg hU)

/-- The old-noise increment has the integrable rate
delta^(1/4) tau^(-3/4), uniformly over bounded matrix profiles. -/
theorem rate {τ δ U : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ)
    (P : Profile d) (hU : P.upper ≤ U) :
    ‖kernel (τ+δ) P-kernel τ P‖^2 ≤ constant d U*δ^(1/4 : ℝ)*τ^(-(3/4 : ℝ)) := by
  have hb := square_bound (θ := 1/8) hτ hτ1 hδ (by norm_num) (by norm_num) P
  have hh : 0 < τ/2 := by positivity
  have he : ((δ/(τ/2))^(1/8 : ℝ))^2*(MatrixAnalyticKernel.constant d P.upper*(τ/2)^(-(1/2 : ℝ)))=
      constant d P.upper*δ^(1/4 : ℝ)*τ^(-(3/4 : ℝ)) := by
    rw [← Real.rpow_mul_natCast (div_nonneg hδ hh.le)]
    norm_num only [Nat.cast_ofNat,show (1/8 : ℝ)*2=1/4 by norm_num]
    rw [Real.div_rpow hδ hh.le,div_eq_mul_inv,← Real.rpow_neg hh.le]
    calc
      _ = MatrixAnalyticKernel.constant d P.upper*δ^(1/4 : ℝ)*
          ((τ/2)^(-(1/4 : ℝ))*(τ/2)^(-(1/2 : ℝ))) := by ring
      _ = MatrixAnalyticKernel.constant d P.upper*δ^(1/4 : ℝ)*(τ/2)^(-(3/4 : ℝ)) := by
        rw [← Real.rpow_add hh]
        norm_num
      _ = _ := by
        rw [Real.div_rpow hτ.le (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [div_eq_mul_inv]
        rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [neg_neg]
        unfold constant
        ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (MatrixAnalyticKernel.constant_mono hU)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
      (Real.rpow_nonneg hδ _)) (Real.rpow_nonneg hτ.le _))

end SHEStochastic.MatrixKernelTimeIncrement
