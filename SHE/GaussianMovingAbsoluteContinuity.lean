module

public import SHE.GaussianTimeLipschitz

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.GaussianMovingAbsoluteContinuity
open Set MeasureTheory GaussianIncrement GaussianConvolution GaussianContinuity
open GaussianTaylor GaussianCovariancePath BackwardRegularity
open scoped MatrixOrder NNReal ENNReal

/-- A moving mean and an ordered covariance with absolutely continuous
trace give an absolutely continuous Gaussian average, even at a terminal
heat singularity. The covariance path need not be Lipschitz. -/
theorem average {n : ℕ} (C : ℝ→PositiveCovariance n)
    (horder : ∀ u v,u≤v→((C u).val-(C v).val).PosSemidef)
    {a b : ℝ} (htrace : AbsolutelyContinuousOnInterval (fun t=>(C t).val.trace) a b)
    (m : ℝ→State n) (Km : ℝ≥0) (hm : LipschitzWith Km m)
    {F : State n→ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z,‖F z‖≤M) (hD : ∀ z,‖fderiv ℝ F z‖≤L)
    (hDD : ∀ z,‖hessian F z‖≤B) (hL : 0≤L) (hB : 0≤B) :
    AbsolutelyContinuousOnInterval (fun t=>gaussianAverage (C t).val F (m t)) a b := by
  let g : ℝ→ℝ:=fun t=>L*(Km:ℝ)*t-B*(C t).val.trace
  have hid : AbsolutelyContinuousOnInterval (fun t:ℝ=>t) a b:=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hg : AbsolutelyContinuousOnInterval g a b:=
    (hid.const_mul (L*(Km:ℝ))).sub (htrace.const_mul B)
  have hordered (u v : ℝ) (huv : u≤v) :
      dist (gaussianAverage (C u).val F (m u)) (gaussianAverage (C v).val F (m v))≤dist (g u) (g v) := by
    have htr : (C v).val.trace≤(C u).val.trace := by
      have ht:=(horder u v huv).trace_nonneg
      rw [Matrix.trace_sub] at ht
      linarith
    have hcov:=ordered_covariance_lipschitz (C u).property (C v).property
      (Or.inl (horder u v huv)) hF hbound hD hDD hB (m v)
    have hmean:=(GaussianTimeLipschitz.mean_lipschitz (C u).val hF hbound hD hDD hL).dist_le_mul (m u) (m v)
    have hmuv:=hm.dist_le_mul u v
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr huv)] at hmuv
    rw [dist_eq_norm] at hmean
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr htr)] at hcov
    have hgb : g u≤g v := by
      dsimp only [g]
      exact sub_le_sub (mul_le_mul_of_nonneg_left huv (mul_nonneg hL Km.2))
        (mul_le_mul_of_nonneg_left htr hB)
    simp only [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr hgb)]
    have hsplit:=norm_sub_le_norm_sub_add_norm_sub
      (gaussianAverage (C u).val F (m u)) (gaussianAverage (C u).val F (m v))
      (gaussianAverage (C v).val F (m v))
    change ‖gaussianAverage (C u).val F (m u)-gaussianAverage (C u).val F (m v)‖≤L*dist (m u) (m v) at hmean
    have hmean':=hmean.trans (mul_le_mul_of_nonneg_left hmuv hL)
    simp only [Real.norm_eq_abs] at hsplit hmean'
    exact hsplit.trans ((add_le_add hmean' hcov).trans_eq (by dsimp only [g];ring))
  apply absolutelyContinuous_of_dist_domination hg (C:=1)
  intro u _ v _
  rw [one_mul]
  rcases le_total u v with huv|hvu
  · exact hordered u v huv
  · simpa only [dist_comm] using hordered v u hvu

end SHE.GaussianMovingAbsoluteContinuity
