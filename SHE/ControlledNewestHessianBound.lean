module
public import SHE.ControlledReferenceFamilyBounds
public import SHE.GaussianSmooth
public import SHE.NormalizedInsertion
public import SHE.GaussianConvolution
public import SHE.CutoffWeightedDerivatives

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.ControlledNewestHessianBound
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledNewestHessianBound_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledNewestHessianBound_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledNewestHessianBound_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)
variable (Λ θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {X:Type}[MeasurableSpace X]{n:ℕ}(Z:VariableObservations.Family X n)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State n=>F z.1 z.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm

/-- A coarse fixed-smooth-word bound used ONLY to justify absolute
Fubini. It is uniform in the actual random past inputs, q and old state,
and retains the genuine integrable old-history weight. Its derivative
constant is never used to select the coefficient approximation index. -/
theorem bound (k:ℕ):∃B:ℝ,0≤B ∧∀(p:Inputs)(h:History X k)(q:ℝ)(z:WordRecursion.State (n+k)),
    ‖WordRecursion.hessian (gaussianAverage
      (WordRecursion.covariance (referenceData P A hA Λ θ v b hvb p).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
      (UncutSmoothWords.test (Base p) k h)) z‖≤B*UncutSmoothWords.weight (Base (0,0)) k h:=by
  have hs:=ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k
  obtain ⟨M,hM,hMb⟩:=hs.norm_bound
  obtain ⟨L,hL,hLb⟩:=hs.fderiv.norm_bound
  obtain ⟨B,hB,hBb⟩:=hs.fderiv.fderiv.norm_bound
  refine ⟨B,hB,?_⟩
  intro p h q z
  let η:=ProbabilityTheory.multivariateGaussian (0:WordRecursion.State (n+k))
    (WordRecursion.covariance (referenceData P A hA Λ θ v b hvb p).reference
      ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
  have hb:=GaussianSmooth.average_hessian_bound η ((hs.smooth (p,h)).of_le (by norm_num))
    (hMb (p,h)) (hLb (p,h)) (hBb (p,h)) z
  rw [UncutSmoothWords.test_eq_weight_normalized]
  change ‖GaussianTaylor.hessian (GaussianSmooth.average η
    (UncutSmoothWords.weight (Base p) k h • UncutSmoothWords.normalized (Base p) k h)) z‖≤_
  rw [NormalizedInsertion.average_smul]
  have hn:=CutoffWeightedDerivatives.norm_hessian_smul_le (UncutSmoothWords.weight (Base p) k h)
    (GaussianSmooth.average η (UncutSmoothWords.normalized (Base p) k h)) z
  rw [abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)] at hn
  have hh:=hn.trans (mul_le_mul_of_nonneg_left hb (UncutSmoothWords.weight_nonneg (Base p) k h))
  exact hh.trans_eq (by
    change UncutSmoothWords.weight (Base p) k h*B=B*UncutSmoothWords.weight (Base (0,0)) k h
    rw [ControlledReferenceFamilyBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
    ring)

end SHE.ControlledNewestHessianBound
