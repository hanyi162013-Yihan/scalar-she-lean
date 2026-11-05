module

public import SHE.GaussianSignedCovariance

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianSignedCovariance
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianTaylor GaussianConvolution
  GaussianCovariancePath
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def traceOperator (n : ℕ) : Mat n →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin n) ℝ ℝ).toContinuousLinearMap

def covarianceBoundConstant (n : ℕ) : ℝ := 2 * (n : ℝ) + ‖traceOperator n‖

theorem covarianceBoundConstant_nonneg (n : ℕ) : 0 ≤ covarianceBoundConstant n := by
  unfold covarianceBoundConstant
  positivity

/-- A genuine global Lipschitz bound for arbitrary PSD covariance pairs.
The covariance increment need not have either sign. -/
theorem unordered_covariance_lipschitz {A C : Mat n}
    (hA : A.PosSemidef) (hC : C.PosSemidef)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖hessian F z‖ ≤ B) (hB : 0 ≤ B) (z : State n) :
    ‖gaussianAverage A F z - gaussianAverage C F z‖ ≤
      B * covarianceBoundConstant n * ‖A - C‖ := by
  let U := commonUpper A C
  have hU : U.PosSemidef := commonUpper_positive A C hC
  have hUA : (U - A).PosSemidef := commonUpper_sub_left_positive A C hA.isHermitian hC.isHermitian
  have hUC : (U - C).PosSemidef := commonUpper_sub_right_positive A C
  have ha := ordered_covariance_lipschitz hA hU (Or.inr hUA) hF hbound hD hDD hB z
  have hc := ordered_covariance_lipschitz hU hC (Or.inl hUC) hF hbound hD hDD hB z
  have hta : 0 ≤ U.trace - A.trace := by simpa only [Matrix.trace_sub] using hUA.trace_nonneg
  have htc : 0 ≤ U.trace - C.trace := by simpa only [Matrix.trace_sub] using hUC.trace_nonneg
  have ht : |A.trace - C.trace| ≤ ‖traceOperator n‖ * ‖A - C‖ := by
    have hh := (traceOperator n).le_opNorm (A - C)
    change ‖(A - C).trace‖ ≤ _ at hh
    simpa only [Matrix.trace_sub, Real.norm_eq_abs] using hh
  have hta' : U.trace - A.trace ≤ ((n : ℝ) + ‖traceOperator n‖) * ‖A - C‖ := by
    have he := commonUpper_trace_left A C
    change U.trace - A.trace = _ at he
    have hn := (abs_le.mp ht).1
    nlinarith
  have htc' : U.trace - C.trace = (n : ℝ) * ‖A - C‖ := commonUpper_trace_right A C
  calc
    _ ≤ ‖gaussianAverage A F z - gaussianAverage U F z‖ +
        ‖gaussianAverage U F z - gaussianAverage C F z‖ := by
      simpa only [dist_eq_norm] using dist_triangle (gaussianAverage A F z) (gaussianAverage U F z) (gaussianAverage C F z)
    _ ≤ B * |A.trace - U.trace| + B * |U.trace - C.trace| := add_le_add ha hc
    _ = B * (U.trace - A.trace) + B * (U.trace - C.trace) := by
      rw [abs_of_nonpos (by linarith : A.trace - U.trace ≤ 0), neg_sub, abs_of_nonneg htc]
    _ ≤ B * (((n : ℝ) + ‖traceOperator n‖) * ‖A - C‖) + B * ((n : ℝ) * ‖A - C‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hta' hB) (le_of_eq (congrArg (fun r => B * r) htc'))
    _ = _ := by unfold covarianceBoundConstant; ring

end SHE.GaussianSignedCovariance
