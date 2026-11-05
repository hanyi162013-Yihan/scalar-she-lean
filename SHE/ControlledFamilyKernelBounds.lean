module

public import SHE.ControlledThetaWordFields
public import SHE.WeightedMeanBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFamilyKernelBounds
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution HistoryProductMeasure
  SmoothCylinders StopWeightedRows PhysicalParentGeometry UniformSmooth
open scoped NNReal
local instance controlledFamilyKernelBounds_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyKernelBounds_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyKernelBounds_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- All actual state gradients have one bound before interpolation and
both past input states are chosen. The only remaining history factor is
the literal uncut row weight. -/
theorem uncut_family_fderiv_bound (k : ℕ) : ∃ M : ℝ,0≤M ∧ ∀ a p z,
    ‖fderiv ℝ (UncutSmoothWords.test (Base a) k p) z‖≤
      M*UncutSmoothWords.weight (Base a) k p := by
  obtain ⟨M,hM,hbound⟩ := (ControlledThetaWordFields.normalized_uniform
    P A hA Λ v b hvb Z htarget hstop F hF hFm k).fderiv.norm_bound
  refine ⟨M,hM,fun a p z=>?_⟩
  rw [UncutSmoothWords.test_eq_weight_normalized,fderiv_const_smul_field]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base a) k p)]
  nlinarith [hbound (a,p) z,UncutSmoothWords.weight_nonneg (Base a) k p]

/-- A genuine Fubini bound for the entire controlled reference family.
It is uniform over arbitrary reference input states, interpolation,
current means and every spatial history. No quantitative cost uses this
coarse bound; closing fixed history time gaps may make it diverge. -/
theorem weightedPoint_family_uniform_bound (k : ℕ) {damping : ℝ} (hdamping : 0≤damping)
    (q r : ℝ) (t : Fin k→ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ a (m : History X k→WordRecursion.State (n+k)) y x z,
      ‖ActualMeanKernel.weightedPoint (Base a) k damping q r m (separated k (x,t,z)) y‖≤B := by
  obtain ⟨M,hM,hbound⟩ := uncut_family_fderiv_bound P A hA Λ v b hvb Z htarget hstop F hF hFm k
  let a0 : ℝ×Inputs := (0,(0,0))
  let R0 := ControlledReferenceLevel.referenceData P A hA Λ a0.1 v b hvb a0.2
  let W := ActualMeanKernel.fixedWeightBound (R:=R0) (n:=n) (b:ℝ) k t
  let τ := ActualMeanKernel.fixedTerminal (R:=R0) (b:ℝ) k t
  have hT (a : ℝ×Inputs) (x : X) : (Base a).terminal x=(b:ℝ) := rfl
  have hterminal (a : ℝ×Inputs) (x : X) (z : Fin k→HeatCircle) :
      (carrier (Base a) k).terminal (separated k (x,t,z))=τ := by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm a a0]
    exact ActualMeanKernel.terminal_separated (Base a0) (b:ℝ) (hT a0) k t x z
  have hW : 0≤W := ActualMeanKernel.fixedWeightBound_nonneg (R:=R0) (n:=n) (b:ℝ) k t
  have hweight (a : ℝ×Inputs) (x : X) (z : Fin k→HeatCircle) :
      UncutSmoothWords.weight (Base a) k (separated k (x,t,z))≤W := by
    rw [ControlledReferenceThetaGeometry.weight_eq P A hA Λ v b hvb Z htarget hstop F hF hFm a a0]
    exact ActualMeanKernel.weight_separated_bound (Base a0) (b:ℝ) (hT a0) k t x z
  by_cases hqr : q<τ ∧ r<τ
  · let V := Real.sqrt (↑(n+k):ℝ)*CovarianceMatrix.heatRowBound (τ-r)
    have hV : 0≤V := mul_nonneg (Real.sqrt_nonneg _)
      (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr hqr.2)).le
    refine ⟨M*W*V,mul_nonneg (mul_nonneg hM hW) hV,?_⟩
    intro a m y x z
    let p := separated k (x,t,z)
    have htp : (carrier (Base a) k).terminal p=τ := hterminal a x z
    have hqa : q<(carrier (Base a) k).terminal p := by rw [htp]; exact hqr.1
    have hra : r<(carrier (Base a) k).terminal p := by rw [htp]; exact hqr.2
    have hr : ‖weightedHeatRow damping ((carrier (Base a) k).observations.observations p) q r y‖≤V :=
      (ActualMeanKernel.weightedHeatRow_norm_le (Base a) k hdamping p hqa r y).trans
        (UniformInsertions.heatRow_norm_bound ((carrier (Base a) k).observations.observations p)
          (t:=r) (sub_pos.mpr hqr.2)
          (fun i=>by linarith [(carrier (Base a) k).targets_after p i]) y)
    have hSmooth := ActualMeanKernel.test_boundedSmooth (Base a) k p
    have hd : ‖fderiv ℝ (gaussianAverage (covariance
        (ControlledReferenceLevel.referenceData P A hA Λ a.1 v b hvb a.2).reference
        ((carrier (Base a) k).observations.observations p) q ((carrier (Base a) k).terminal p))
        (UncutSmoothWords.test (Base a) k p)) (m p)‖≤M*UncutSmoothWords.weight (Base a) k p :=
      GaussianSmooth.average_fderiv_bound _ (hSmooth.smooth.of_le (by simp))
        hSmooth.norm_bound.choose_spec (hbound a p) _
    rw [ActualMeanKernel.weightedPoint_of_active (Base a) k damping q r m p y hqa hra]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left (hweight a x z) hM)) hr
        (norm_nonneg _) (mul_nonneg hM hW))
  · refine ⟨0,le_rfl,?_⟩
    intro a m y x z
    simp only [ActualMeanKernel.weightedPoint,hterminal,if_neg hqr,norm_zero]
    exact le_rfl

theorem weightedSpatial_family_uniform_bound (k : ℕ) {damping : ℝ} (hdamping : 0≤damping)
    (q r : ℝ) (t : Fin k→ℝ) :
    ∃ B : ℝ,0≤B ∧ ∀ a (m : History X k→WordRecursion.State (n+k)) y x,
      ‖ActualMeanKernel.weightedSpatial (Base a) k damping q r (fun _ : Unit=>m) t () y x‖≤B := by
  obtain ⟨B,hB,hbound⟩ := weightedPoint_family_uniform_bound P A hA Λ v b hvb Z htarget hstop F hF hFm k hdamping q r t
  refine ⟨B,hB,fun a m y x=>?_⟩
  change ‖(((∫ z : Fin k→HeatCircle,ActualMeanKernel.weightedPoint (Base a) k damping q r m
    (separated k (x,t,z)) y ∂Measure.pi (fun _=>AddCircle.haarAddCircle)) : ℝ) : ℂ)‖≤_
  rw [Complex.norm_real,Real.norm_eq_abs]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin k=>AddCircle.haarAddCircle))
      (f:=fun z=>ActualMeanKernel.weightedPoint (Base a) k damping q r m (separated k (x,t,z)) y)
      (C:=B) (ae_of_all _ (fun z=>hbound a m y x z))

end SHE.ControlledFamilyKernelBounds
