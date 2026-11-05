module

public import SHE.ActualMeanKernelBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders
local instance actualMeanPointBounds_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- A coarse Fubini bound for the literal point kernel before old-space
averaging. It is uniform over every current mean, physical input/output,
and insertion location, for each fixed original time list. -/
theorem point_uniform_bound (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : ℝ) (t : Fin k → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : Ω → History P k → WordRecursion.State (n+k)) ω y p x,
      ‖point L k q (m ω) (separated k (p,t,x)) y‖ ≤ B := by
  obtain ⟨M,hM,hbound⟩ := uncut_fderiv_bound L k
  let W := fixedWeightBound (R:=R) (n:=n) T k t
  let τ := fixedTerminal (R:=R) T k t
  by_cases hq : q<τ
  · let V := Real.sqrt (↑(n+k):ℝ)*CovarianceMatrix.heatRowBound (τ-q)
    have hV : 0 ≤ V := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr hq)).le
    refine ⟨M*W*V,mul_nonneg (mul_nonneg hM (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)) hV,?_⟩
    intro m ω y p x
    let a := separated k (p,t,x)
    have hterminal : (carrier L k).terminal a=τ := terminal_separated L T hT k t p x
    have hr : ‖heatRow ((carrier L k).observations.observations a) q y‖ ≤ V :=
      UniformInsertions.heatRow_norm_bound ((carrier L k).observations.observations a) (t:=q) (sub_pos.mpr hq)
        (fun i => by linarith [(carrier L k).targets_after a i]) y
    have hF := test_boundedSmooth L k a
    have hd : ‖fderiv ℝ (gaussianAverage (covariance R.reference
        ((carrier L k).observations.observations a) q ((carrier L k).terminal a))
        (UncutSmoothWords.test L k a)) (m ω a)‖ ≤ M*UncutSmoothWords.weight L k a :=
      GaussianSmooth.average_fderiv_bound _ (hF.smooth.of_le (by simp))
        (hF.norm_bound.choose_spec) (hbound a) _
    rw [point_of_before L k q (m ω) a y (by simpa only [hterminal] using hq)]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left (weight_separated_bound L T hT k t p x) hM))
        hr (norm_nonneg _) (mul_nonneg hM (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)))
  · refine ⟨0,le_rfl,?_⟩
    intro m ω y p x
    change ¬ q<fixedTerminal (R:=R) T k t at hq
    simp only [point,terminal_separated L T hT,if_neg hq,norm_zero]
    exact le_rfl

end SHE.ActualMeanKernel
