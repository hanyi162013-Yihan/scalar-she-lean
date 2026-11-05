module

public import SHE.ActualMeanKernel
public import SHE.WeightedMeanKernel
public import SHE.CarrierGeometryCongruence

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.RootWordLinearity
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution GaussianSmooth SmoothCylinders CutoffInsertionCore

/-- Actual Gaussian averaging is additive in its root test. -/
theorem gaussianAverage_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {F G : WordRecursion.State n→ℝ} (hF : BoundedSmooth F) (hG : BoundedSmooth G) :
    gaussianAverage A (F+G)=gaussianAverage A F+gaussianAverage A G := by
  funext z
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨N,hN⟩:=hG.norm_bound
  exact integral_add (integrable_translate _ hF.smooth.continuous hM z)
    (integrable_translate _ hG.smooth.continuous hN z)

theorem average_boundedSmooth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {F : WordRecursion.State n→ℝ} (hF : BoundedSmooth F) : BoundedSmooth (gaussianAverage A F):=
  hF.average _

/-- The literal Hessian insertion is additive in the entire test. -/
theorem core_add {n : ℕ} (a : ℝ→ℝ) (reference : ℝ) (row : WordRecursion.State n)
    {F G : WordRecursion.State n→ℝ} (hF : BoundedSmooth F) (hG : BoundedSmooth G) :
    core a reference row (F+G)=core a reference row F+core a reference row G := by
  have he : fderiv ℝ (F+G)=fderiv ℝ F+fderiv ℝ G:=by
    funext x
    exact fderiv_add (hF.smooth.differentiable (by simp) x) (hG.smooth.differentiable (by simp) x)
  funext z
  unfold core directionalSecond WordRecursion.hessian
  rw [he,fderiv_add (hF.fderiv.smooth.differentiable (by simp) _)
    (hG.fderiv.smooth.differentiable (by simp) _)]
  simp only [ContinuousLinearMap.add_apply,Pi.add_apply]
  ring

variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L K : Level R X n) (hT : ∀ x,L.terminal x=K.terminal x)
    (hZ : ∀ x,L.observations.observations x=K.observations.observations x)
include hT hZ

theorem nodeCovariance_val (k : ℕ) (p : History X (k+1)) :
    ((carrier L k).nodeCovariance p).val=((carrier K k).nodeCovariance p).val := by
  change covariance R.reference ((carrier L k).observations.observations p.1)
      ((carrier L k).nodeTime p) ((carrier L k).terminal p.1)=_
  rw [CarrierGeometryCongruence.observations L K rfl hT hZ k p.1,
    CarrierGeometryCongruence.nodeTime L K rfl hT k p,
    CarrierGeometryCongruence.terminal L K rfl hT k p.1]
  rfl

variable (M : Level R X n) (hTM : ∀ x,L.terminal x=M.terminal x)
    (hZM : ∀ x,L.observations.observations x=M.observations.observations x)
include hTM hZM

/-- Root additivity of the ACTUAL uncut recursive word at every finite
depth, with all original physical observations and covariance insertions.
Only the initial tests are related; the conclusion is proved recursively. -/
theorem test_add (hroot : ∀ x,L.test x=K.test x+M.test x) (k : ℕ) (p : History X k) :
    UncutSmoothWords.test L k p=UncutSmoothWords.test K k p+UncutSmoothWords.test M k p := by
  induction k with
  | zero=>exact hroot p
  | succ k ih=>
    change core R.totalVariance (R.reference ((carrier L k).nodeTime p,p.2.2)) (CutoffCarriers.row L k p)
        (gaussianAverage ((carrier L k).nodeCovariance p).val (UncutSmoothWords.test L k p.1))=
      core R.totalVariance (R.reference ((carrier K k).nodeTime p,p.2.2)) (CutoffCarriers.row K k p)
        (gaussianAverage ((carrier K k).nodeCovariance p).val (UncutSmoothWords.test K k p.1))+
      core R.totalVariance (R.reference ((carrier M k).nodeTime p,p.2.2)) (CutoffCarriers.row M k p)
        (gaussianAverage ((carrier M k).nodeCovariance p).val (UncutSmoothWords.test M k p.1))
    rw [←CarrierGeometryCongruence.nodeTime L K rfl hT k p,
      ←CarrierGeometryCongruence.nodeTime L M rfl hTM k p,
      ←CarrierGeometryCongruence.row L K rfl hT hZ k p,
      ←CarrierGeometryCongruence.row L M rfl hTM hZM k p,
      ←nodeCovariance_val L K hT hZ k p,←nodeCovariance_val L M hTM hZM k p,ih p.1]
    have hK:=ActualMeanKernel.test_boundedSmooth K k p.1
    have hM:=ActualMeanKernel.test_boundedSmooth M k p.1
    rw [gaussianAverage_add _ hK hM,core_add _ _ _ (average_boundedSmooth _ hK) (average_boundedSmooth _ hM)]

theorem cappedAverage_add (hroot : ∀ x,L.test x=K.test x+M.test x)
    (k : ℕ) (q : ℝ) (p : History X k) :
    ActualMeanKernel.cappedAverage L k q p=
      ActualMeanKernel.cappedAverage K k q p+ActualMeanKernel.cappedAverage M k q p := by
  unfold ActualMeanKernel.cappedAverage
  rw [test_add L K hT hZ M hTM hZM hroot k p,
    gaussianAverage_add _ (ActualMeanKernel.test_boundedSmooth K k p) (ActualMeanKernel.test_boundedSmooth M k p)]
  rw [CarrierGeometryCongruence.observations L K rfl hT hZ k p,
    CarrierGeometryCongruence.terminal L K rfl hT k p]
  have hKMterm (x) : K.terminal x=M.terminal x:=(hT x).symm.trans (hTM x)
  have hKMobs (x) : K.observations.observations x=M.observations.observations x:=(hZ x).symm.trans (hZM x)
  rw [CarrierGeometryCongruence.observations K M rfl hKMterm hKMobs k p,
    CarrierGeometryCongruence.terminal K M rfl hKMterm k p]

end SHE.RootWordLinearity
