module

public import SHE.SeparatedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders
local instance separatedMeanBounds_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P X : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The later direction row has a finite fixed-time Fubini bound while
the Gaussian law and current mean stay at q. Inactive extensions make
the statement valid for every pair q,r and every old time list. -/
theorem rowPoint_uniform_bound (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q r : ℝ) (t : Fin k → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : X → History P k → WordRecursion.State (n+k)) x y p z,
      ‖rowPoint L k q r (m x) (separated k (p,t,z)) y‖ ≤ B := by
  obtain ⟨M,hM,hbound⟩ := uncut_fderiv_bound L k
  let W := fixedWeightBound (R:=R) (n:=n) T k t
  let τ := fixedTerminal (R:=R) T k t
  by_cases hq : q<τ ∧ r<τ
  · let V := Real.sqrt (↑(n+k):ℝ)*CovarianceMatrix.heatRowBound (τ-r)
    have hV : 0 ≤ V := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr hq.2)).le
    refine ⟨M*W*V,mul_nonneg (mul_nonneg hM (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)) hV,?_⟩
    intro m x y p z
    let a := separated k (p,t,z)
    have hterminal : (carrier L k).terminal a=τ := terminal_separated L T hT k t p z
    have hr : ‖heatRow ((carrier L k).observations.observations a) r y‖ ≤ V :=
      UniformInsertions.heatRow_norm_bound ((carrier L k).observations.observations a) (t:=r) (sub_pos.mpr hq.2)
        (fun i => by linarith [(carrier L k).targets_after a i]) y
    have hF := test_boundedSmooth L k a
    have hd : ‖fderiv ℝ (gaussianAverage (covariance R.reference
        ((carrier L k).observations.observations a) q ((carrier L k).terminal a))
        (UncutSmoothWords.test L k a)) (m x a)‖ ≤ M*UncutSmoothWords.weight L k a :=
      GaussianSmooth.average_fderiv_bound _ (hF.smooth.of_le (by simp))
        (hF.norm_bound.choose_spec) (hbound a) _
    rw [rowPoint_of_active L k q r (m x) a y
      (by simpa only [hterminal] using hq.1) (by simpa only [hterminal] using hq.2)]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left (weight_separated_bound L T hT k t p z) hM))
        hr (norm_nonneg _) (mul_nonneg hM (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)))
  · refine ⟨0,le_rfl,?_⟩
    intro m x y p z
    change ¬(q<fixedTerminal (R:=R) T k t ∧ r<fixedTerminal (R:=R) T k t) at hq
    simp only [rowPoint,terminal_separated L T hT,if_neg hq,norm_zero]
    exact le_rfl

theorem rowSpatial_uniform_bound (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q r : ℝ) (t : Fin k → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : X → History P k → WordRecursion.State (n+k)) x y p,
      ‖rowSpatial L k q r m t x y p‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := rowPoint_uniform_bound L (X:=X) T hT k q r t
  refine ⟨B,hB,fun m x y p => ?_⟩
  change ‖(((∫ z : Fin k → HeatCircle,rowPoint L k q r (m x) (separated k (p,t,z)) y
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real,Real.norm_eq_abs]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
      (f:=fun z => rowPoint L k q r (m x) (separated k (p,t,z)) y) (C:=B)
      (ae_of_all _ (fun z => hbound m x y p z))

end SHE.ActualMeanKernel
