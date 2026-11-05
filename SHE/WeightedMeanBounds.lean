module

public import SHE.WeightedMeanKernel
public import SHE.SeparatedMeanBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders StopWeightedRows PhysicalParentGeometry
local instance weightedMeanBounds_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P X : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual damping weights are contractions before every active
stopping time; no covariance-range assertion is needed here. -/
theorem weightedHeatRow_norm_le (k : ℕ) {Λ q : ℝ} (hΛ : 0≤Λ)
    (p : History P k) (hq : q < (carrier L k).terminal p) (r : ℝ) (y : HeatCircle) :
    ‖weightedHeatRow Λ ((carrier L k).observations.observations p) q r y‖ ≤
      ‖heatRow ((carrier L k).observations.observations p) r y‖ := by
  apply diagonal_norm_le
  intro i
  rw [abs_of_pos (weights_pos Λ _ q i)]
  exact weights_le_one hΛ _ q (fun j => hq.le.trans ((carrier L k).stops_after p j)) i

/-- A genuine coarse Fubini bound, uniform in the current mean, input,
output and old spatial history. It uses only bounded smooth finite tests
and the literal heat-row bound. -/
theorem weightedPoint_uniform_bound (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q r : ℝ) (t : Fin k → ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ (m : X → History P k → WordRecursion.State (n+k)) x y p z,
      ‖weightedPoint L k Λ q r (m x) (separated k (p,t,z)) y‖ ≤ B := by
  obtain ⟨M,hM,hbound⟩ := uncut_fderiv_bound L k
  let W := fixedWeightBound (R:=R) (n:=n) T k t
  let τ := fixedTerminal (R:=R) T k t
  by_cases hq : q<τ ∧ r<τ
  · let V := Real.sqrt (↑(n+k):ℝ)*CovarianceMatrix.heatRowBound (τ-r)
    have hV : 0≤V := mul_nonneg (Real.sqrt_nonneg _)
      (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr hq.2)).le
    refine ⟨M*W*V,mul_nonneg (mul_nonneg hM
      (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)) hV,?_⟩
    intro m x y p z
    let a := separated k (p,t,z)
    have hterminal : (carrier L k).terminal a=τ := terminal_separated L T hT k t p z
    have hqa : q < (carrier L k).terminal a := by simpa only [hterminal] using hq.1
    have hra : r < (carrier L k).terminal a := by simpa only [hterminal] using hq.2
    have hr : ‖weightedHeatRow Λ ((carrier L k).observations.observations a) q r y‖ ≤ V :=
      (weightedHeatRow_norm_le L k hΛ a hqa r y).trans
        (UniformInsertions.heatRow_norm_bound ((carrier L k).observations.observations a)
          (t:=r) (sub_pos.mpr hq.2)
          (fun i => by linarith [(carrier L k).targets_after a i]) y)
    have hF := test_boundedSmooth L k a
    have hd : ‖fderiv ℝ (gaussianAverage (covariance R.reference
        ((carrier L k).observations.observations a) q ((carrier L k).terminal a))
        (UncutSmoothWords.test L k a)) (m x a)‖ ≤ M*UncutSmoothWords.weight L k a :=
      GaussianSmooth.average_fderiv_bound _ (hF.smooth.of_le (by simp))
        (hF.norm_bound.choose_spec) (hbound a) _
    rw [weightedPoint_of_active L k Λ q r (m x) a y hqa hra]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left
        (weight_separated_bound L T hT k t p z) hM))
        hr (norm_nonneg _) (mul_nonneg hM (fixedWeightBound_nonneg (R:=R) (n:=n) T k t)))
  · refine ⟨0,le_rfl,?_⟩
    intro m x y p z
    change ¬(q<fixedTerminal (R:=R) T k t ∧ r<fixedTerminal (R:=R) T k t) at hq
    simp only [weightedPoint,terminal_separated L T hT,ite_eq_right hq,norm_zero]
    exact le_rfl

theorem weightedSpatial_uniform_bound (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q r : ℝ) (t : Fin k → ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ (m : X → History P k → WordRecursion.State (n+k)) x y p,
      ‖weightedSpatial L k Λ q r m t x y p‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := weightedPoint_uniform_bound L (X:=X) T hT k hΛ q r t
  refine ⟨B,hB,fun m x y p => ?_⟩
  change ‖(((∫ z : Fin k → HeatCircle,weightedPoint L k Λ q r (m x) (separated k (p,t,z)) y
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real,Real.norm_eq_abs]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
      (f:=fun z => weightedPoint L k Λ q r (m x) (separated k (p,t,z)) y) (C:=B)
      (ae_of_all _ (fun z => hbound m x y p z))

theorem weightedPoint_zero_of_not_strict (k : ℕ) (Λ q r : ℝ)
    (m : History P k → WordRecursion.State (n+k)) (p : History P k) (y : HeatCircle)
    (hp : ¬StrictHistory L k p) : weightedPoint L k Λ q r m p y=0 := by
  simp only [weightedPoint,test_zero_of_not_strict L k p hp]
  have hz (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ) :
      gaussianAverage A (0 : WordRecursion.State (n+k) → ℝ)=fun _ => 0 := by
    funext z
    simp [gaussianAverage]
  have hd : fderiv ℝ (fun _ : WordRecursion.State (n+k) => (0:ℝ)) (m p)=0 :=
    (hasFDerivAt_const (0:ℝ) (m p)).fderiv
  simp only [hz,hd,ContinuousLinearMap.zero_apply,ite_self]

end SHE.ActualMeanKernel
