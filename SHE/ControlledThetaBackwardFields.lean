module

public import SHE.ControlledThetaWordFields
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHE.ControlledThetaBackwardFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
  SmoothCylinders UniformSmooth GaussianContinuity
open scoped NNReal
local instance controlledThetaBackwardFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaBackwardFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaBackwardFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The actual capped backward average, jointly in theta, both past
inputs, law time, original history and current finite-dimensional mean. -/
theorem value_joint_measurable (k : ℕ) : Measurable
    (fun z : (((ℝ×Inputs)×(ℝ×History X k))×WordRecursion.State (n+k))=>
      ActualMeanKernel.cappedAverage (Base z.1.1) k z.1.2.1 z.1.2.2 z.2) := by
  let Ξ:=(ℝ×Inputs)×(ℝ×History X k)
  let S : VariableObservations.Family Ξ (n+k):=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun p : Ξ=>(p.1,p.2.2)) (measurable_fst.prodMk measurable_snd.snd)
  have hc : Measurable (fun p : Ξ×(ℝ×HeatCircle)=>
      ControlledReferenceWindows.coefficient P Λ p.1.1.1 v p.1.1.2 p.2) := by
    have hm:=ControlledThetaWordFields.coefficient_joint_measurable P Λ v
    have hmap : Measurable (fun p : Ξ×(ℝ×HeatCircle)=>(p.1.1,p.2)):=
      measurable_fst.fst.prodMk measurable_snd
    have hh:=hm.comp hmap
    exact hh
  have hT : Measurable (fun p : Ξ=>(carrier (Base p.1) k).terminal p.2.2) := by
    have hm:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    have hmap : Measurable (fun p : Ξ=>(p.1,p.2.2)):=measurable_fst.prodMk measurable_snd.snd
    have hh:=hm.comp hmap
    exact hh
  have hC:=S.covariance_measurable hc (measurable_snd.fst.min hT) hT (fun _=>min_le_right _ _)
  let M := fun z : Ξ×WordRecursion.State (n+k)=>WordRecursion.covariance
    (ControlledReferenceWindows.coefficient P Λ z.1.1.1 v z.1.1.2)
    ((carrier (Base z.1.1) k).observations.observations z.1.2.2)
    (min z.1.2.1 ((carrier (Base z.1.1) k).terminal z.1.2.2))
    ((carrier (Base z.1.1) k).terminal z.1.2.2)
  have hM : Measurable M := by
    have hh:=hC.comp (measurable_fst : Measurable (Prod.fst : Ξ×WordRecursion.State (n+k)→Ξ))
    convert hh using 1
    rfl
  have htest : Measurable (fun z : (Ξ×WordRecursion.State (n+k))×WordRecursion.State (n+k)=>
      UncutSmoothWords.test (Base z.1.1.1) k z.1.1.2.2 (z.1.2+z.2)) := by
    have hm:=ControlledThetaWordFields.test_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    have hmap : Measurable (fun z : (Ξ×WordRecursion.State (n+k))×WordRecursion.State (n+k)=>
      ((z.1.1.1,z.1.1.2.2),z.1.2+z.2)) :=
      (measurable_fst.fst.fst.prodMk measurable_fst.fst.snd.snd).prodMk
        (measurable_fst.snd.add measurable_snd)
    have hh:=hm.comp hmap
    exact hh
  have hh:=(htest.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=GaussianScoreKernel.gaussianKernel M hM)).measurable
  exact hh

/-- Genuine joint Borel gradient of the WHOLE theta-varying recursive
Gaussian word. No fixed-level derivative theorem is applied to a moving
level without proving its joint parameter dependence first. -/
theorem gradient_joint_measurable (k : ℕ) : Measurable
    (fun z : (((ℝ×Inputs)×(ℝ×History X k))×WordRecursion.State (n+k))=>
      fderiv ℝ (ActualMeanKernel.cappedAverage (Base z.1.1) k z.1.2.1 z.1.2.2) z.2) :=
  MeasurableDerivatives.fderiv_measurable (n:=n+k)
    (F:=fun p : (ℝ×Inputs)×(ℝ×History X k)=>ActualMeanKernel.cappedAverage (Base p.1) k p.2.1 p.2.2)
    (value_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun z=>ActualMeanKernel.cappedAverage_differentiable (Base z.1) k z.2.1 z.2.2)

theorem hessian_joint_measurable (k : ℕ) : Measurable
    (fun z : (((ℝ×Inputs)×(ℝ×History X k))×WordRecursion.State (n+k))=>
      GaussianTaylor.hessian (ActualMeanKernel.cappedAverage (Base z.1.1) k z.1.2.1 z.1.2.2) z.2) := by
  apply MeasurableDerivatives.hessian_measurable (n:=n+k)
    (F:=fun p : (ℝ×Inputs)×(ℝ×History X k)=>ActualMeanKernel.cappedAverage (Base p.1) k p.2.1 p.2.2)
    (value_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k)
  intro z
  exact ((ActualMeanKernel.test_boundedSmooth (Base z.1) k z.2.2).average
    (multivariateGaussian (0 : WordRecursion.State (n+k)) _)).smooth.of_le (by simp)

end SHE.ControlledThetaBackwardFields
