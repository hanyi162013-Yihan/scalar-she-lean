module

public import SHE.GaussianReserveAverage
public import SHE.GaussianSmoothCovarianceBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianRangeSmooth
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution GaussianContinuity
  GaussianSignedCovariance
open scoped MatrixOrder Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- A Lipschitz PSD covariance path with a fixed physical Gaussian reserve
gives a genuinely Lipschitz bounded-Borel expectation, at arbitrary means. -/
theorem exists_lipschitz_borel_reserve {R : Mat n} (hR : R.PosSemidef)
    (C : ℝ → PositiveCovariance n) {K : ℝ≥0}
    (hC : LipschitzWith K (fun θ => (C θ).val))
    (hrange : ∀ θ, (Matrix.toEuclideanCLM (𝕜 := ℝ) (C θ).val).range ≤
      (Matrix.toEuclideanCLM (𝕜 := ℝ) R).range)
    (F : State n → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ y, |F y| ≤ M) (z : State n) :
    ∃ L : ℝ≥0, LipschitzWith L (fun θ => gaussianAverage (R + (C θ).val) F z) := by
  let Fz : State n → ℝ := fun y => F (z + y)
  have hm : Measurable Fz := hF.comp (measurable_const.add measurable_id)
  have hb : ∀ y, |Fz y| ≤ M := fun y => hM _
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  have hB0 : 0 ≤ M * extensionJetConstant R 2 := mul_nonneg hM0 (extensionJetConstant_nonneg R 2)
  obtain ⟨hs, h0, h1, h2, _, _⟩ := extension_covariance_regularity hR Fz hm hb
  let B := M * extensionJetConstant R 2
  have hB : 0 ≤ B := hB0
  have hL : 0 ≤ B * covarianceBoundConstant n := mul_nonneg hB (covarianceBoundConstant_nonneg n)
  refine ⟨Real.nnabs (B * covarianceBoundConstant n) * K, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  have he (s : ℝ) : gaussianAverage (C s).val (roughAverageExtension R Fz) 0 =
      gaussianAverage (R + (C s).val) F z := by
    have hh := reserve_average hR (C s).property (hrange s) Fz hm M hb (Submodule.zero_mem _)
    simpa only [gaussianAverage, Fz, zero_add] using hh
  rw [Real.dist_eq, ← he θ, ← he η]
  have hh := unordered_covariance_lipschitz (C θ).property (C η).property hs h0 h1 h2 hB 0
  have hl := mul_le_mul_of_nonneg_left (hC.norm_sub_le θ η) hL
  apply hh.trans
  convert! hl using 1
  simp only [NNReal.coe_mul, Real.coe_nnabs, abs_of_nonneg hL, Real.norm_eq_abs, Real.dist_eq]
  ring

end SHE.GaussianRangeSmooth
