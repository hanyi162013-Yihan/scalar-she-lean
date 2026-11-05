module

public import SHE.ActualMeanKernel
public import SHE.UniformInsertions

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers GaussianConvolution HistoryProductMeasure
  SmoothCylinders PhysicalParentGeometry
local instance actualMeanKernelBounds_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual clipped terminal time depends only on the fixed original
terminal and history times, and never on the spatial history. -/
def fixedTerminal (T : ℝ) : (k : ℕ) → (Fin k → ℝ) → ℝ
  | 0,_ => T
  | k+1,t => ClippedCovariance.clip R.base (fixedTerminal T k (fun i => t i.succ)) (t 0)

theorem terminal_separated (T : ℝ) (hT : ∀ p, L.terminal p=T) (k : ℕ)
    (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle) :
    (carrier L k).terminal (separated k (p,t,x))=fixedTerminal (R:=R) T k t := by
  induction k with
  | zero => exact hT p
  | succ k ih =>
    change ClippedCovariance.clip R.base
      ((carrier L k).terminal (separated k (p,(fun i => t i.succ),(fun i => x i.succ)))) (t 0)=_
    rw [ih]
    rfl

/-- A finite coarse bound, used only for Fubini. The displayed recursive
constant may diverge as a fixed time gap closes; no such constant enters
the sharp normalized-amplitude estimate. -/
def fixedWeightBound (T : ℝ) : (k : ℕ) → (Fin k → ℝ) → ℝ
  | 0,_ => 1
  | k+1,t =>
    if R.base<t 0 ∧ t 0<fixedTerminal (R:=R) T k (fun i => t i.succ) then
      fixedWeightBound T k (fun i => t i.succ)*
        (Real.sqrt (↑(n+k):ℝ)*CovarianceMatrix.heatRowBound
          (fixedTerminal (R:=R) T k (fun i => t i.succ)-t 0))^2
    else 0

theorem fixedWeightBound_nonneg (T : ℝ) (k : ℕ) (t : Fin k → ℝ) :
    0 ≤ fixedWeightBound (R:=R) (n:=n) T k t := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    simp only [fixedWeightBound]
    split_ifs
    · exact mul_nonneg (ih _) (sq_nonneg _)
    · exact le_rfl

theorem weight_separated_bound (T : ℝ) (hT : ∀ p, L.terminal p=T) (k : ℕ)
    (t : Fin k → ℝ) (p : P) (x : Fin k → HeatCircle) :
    UncutSmoothWords.weight L k (separated k (p,t,x)) ≤ fixedWeightBound (R:=R) (n:=n) T k t := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    let p' : History P k := separated k (p,(fun i => t i.succ),(fun i => x i.succ))
    have ht := terminal_separated L T hT k (fun i => t i.succ) p (fun i => x i.succ)
    change UncutSmoothWords.weight L k p' * ‖row L k (p',t 0,x 0)‖^2 ≤ _
    change (carrier L k).terminal p'=fixedTerminal (R:=R) T k (fun i => t i.succ) at ht
    by_cases hg : R.base<t 0 ∧ t 0<fixedTerminal (R:=R) T k (fun i => t i.succ)
    · have hi : Interior L k (p',t 0,x 0) := ⟨hg.1,by simpa only [ht] using hg.2⟩
      have hd : 0 < fixedTerminal (R:=R) T k (fun i => t i.succ)-t 0 := sub_pos.mpr hg.2
      have htime : (carrier L k).nodeTime (p',t 0,x 0)=t 0 :=
        ClippedCovariance.clip_eq ⟨hi.1.le,hi.2.le⟩
      have hr := UniformInsertions.heatRow_norm_bound ((carrier L k).observations.observations p') (t:=t 0) hd
        (fun i => by linarith [(carrier L k).targets_after p' i]) (x 0)
      simp only [fixedWeightBound,if_pos hg,row,if_pos hi,htime]
      exact mul_le_mul (ih _ _)
        (pow_le_pow_left₀ (norm_nonneg _) hr 2) (sq_nonneg _)
        (fixedWeightBound_nonneg (R:=R) (n:=n) T k _)
    · have hi : ¬ Interior L k (p',t 0,x 0) := by simpa only [Interior,ht] using hg
      simp only [fixedWeightBound,if_neg hg,row,if_neg hi,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]
      exact le_rfl

theorem uncut_fderiv_bound (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ p z,
    ‖fderiv ℝ (UncutSmoothWords.test L k p) z‖ ≤ M*UncutSmoothWords.weight L k p := by
  obtain ⟨M,hM,hbound⟩ := (UncutSmoothWords.normalized_uniform L k).fderiv.norm_bound
  refine ⟨M,hM,fun p z => ?_⟩
  rw [UncutSmoothWords.test_eq_weight_normalized,fderiv_const_smul_field]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (UncutSmoothWords.weight_nonneg L k p)]
  nlinarith [hbound p z,UncutSmoothWords.weight_nonneg L k p]

/-- A genuine uniform bound for the literal derivative and its old-space
average, for arbitrary current means and every fixed original time list.
Only a common initial terminal is required; all inactive/nonordered
histories are handled by the actual zero extension. -/
theorem spatial_uniform_bound (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : ℝ) (t : Fin k → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : Ω → History P k → WordRecursion.State (n+k)) ω y p,
      ‖spatial L k q m t ω y p‖ ≤ B := by
  obtain ⟨M,hM,hbound⟩ := uncut_fderiv_bound L k
  let W := fixedWeightBound (R:=R) (n:=n) T k t
  let τ := fixedTerminal (R:=R) T k t
  by_cases hq : q<τ
  · let V := Real.sqrt (↑(n+k):ℝ)*CovarianceMatrix.heatRowBound (τ-q)
    have hV : 0 ≤ V := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr hq)).le
    refine ⟨M*W*V,mul_nonneg (mul_nonneg hM (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)) hV,?_⟩
    intro m ω y p
    have hp (x : Fin k → HeatCircle) : |point L k q (m ω) (separated k (p,t,x)) y| ≤ M*W*V := by
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
    change ‖(((∫ x : Fin k → HeatCircle,point L k q (m ω) (separated k (p,t,x)) y
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
        (f:=fun x => point L k q (m ω) (separated k (p,t,x)) y) (C:=M*W*V)
        (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hp x))
  · refine ⟨0,le_rfl,?_⟩
    intro m ω y p
    have hz (x : Fin k → HeatCircle) : point L k q (m ω) (separated k (p,t,x)) y=0 := by
      change ¬ q<fixedTerminal (R:=R) T k t at hq
      simp only [point,terminal_separated L T hT,if_neg hq]
    simp only [spatial,hz,integral_zero,Complex.ofReal_zero,norm_zero]
    exact le_rfl

end SHE.ActualMeanKernel
