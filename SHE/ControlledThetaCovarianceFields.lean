module

public import SHE.ControlledThetaWordFields
public import SHE.ControlledThetaPhysicalGeometry
public import SHE.ActualCovarianceMarkFields
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHE.ControlledThetaCovarianceFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
  SmoothCylinders UniformSmooth GaussianContinuity PhysicalChainArrays ControlledReferenceLevel
open scoped NNReal
local instance controlledThetaCovarianceFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaCovarianceFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaCovarianceFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Actual interval covariance arrays of a moving canonical family are
jointly Borel even when the profile depends on every outer parameter. -/
theorem covariances_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c) (j : Fin k) :
    Measurable (fun w=>covariances (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w))
      (fun r=>c (w,r)) k (h w) j) := by
  let S:=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  have hg:=PhysicalChainArrays.covariances_measurable (Base (0,(0,0))) S c hc k h hh j
  convert hg using 1
  funext w
  exact congrFun (ControlledThetaPhysicalGeometry.covariances_eq
    P A hA Λ v b hvb Z htarget hstop F hF hFm (p w) (0,(0,0))
      ((carrier (Base (p w)) k).observations.observations (h w)) (fun r=>c (w,r)) k (h w)) j

/-- Original physical directions have one joint Borel realization for
all theta and past input values, without choosing a physical chain. -/
theorem directions_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h) (j : Fin k) :
    Measurable (fun w=>directions (Base (p w))
      ((carrier (Base (p w)) k).observations.observations (h w)) k (h w) j) := by
  let S:=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  have hg:=PhysicalChainArrays.directions_measurable (Base (0,(0,0))) S k h hh j
  convert hg using 1
  funext w
  exact congrFun (ControlledThetaPhysicalGeometry.directions_eq
    P A hA Λ v b hvb Z htarget hstop F hF hFm (p w) (0,(0,0))
      ((carrier (Base (p w)) k).observations.observations (h w)) k (h w)) j

/-- Literal full residual covariance, with its Borel lower-time cap,
for a genuinely moving canonical reference and an arbitrary joint old
profile. This is proved before any common-event covariance identity. -/
theorem capped_residual_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c) :
    Measurable (fun w=>ActualCovarianceMarkFields.cappedResidual (Base (p w)) (fun r=>c (w,r)) k (h w) (q w)) := by
  let S:=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  have ht : Measurable (fun w=>(carrier (Base (p w)) k).terminal (h w)) := by
    have hm:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    have hmap : Measurable (fun w=>(p w,h w)):=hp.prodMk hh
    have hh':=hm.comp hmap
    exact hh'
  have hr : Measurable (fun z : W×StoppedGaussianFeatures.Domain=>
      (referenceData P A hA Λ (p z.1).1 v b hvb (p z.1).2).reference z.2) := by
    have hm:=ControlledThetaWordFields.coefficient_joint_measurable P Λ v
    have hmap : Measurable (fun z : W×StoppedGaussianFeatures.Domain=>(p z.1,z.2)):=
      (hp.comp measurable_fst).prodMk measurable_snd
    have hh':=hm.comp hmap
    exact hh'
  have hC:=S.covariance_measurable hr (hq.min ht) ht (fun _=>min_le_right _ _)
  have hA (j : Fin k):=covariances_variable_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm
    k p hp h hh (fun z=>(referenceData P A hA Λ (p z.1).1 v b hvb (p z.1).2).reference z.2-c z) (hr.sub hc) j
  apply Measurable.of_eval_matrix
  intro i j
  have hs:=Finset.measurable_sum Finset.univ (fun l _=>(hA l).eval_matrix (i:=i) (j:=j))
  have hg:=(hC.eval_matrix (i:=i) (j:=j)).add hs
  convert hg using 1
  funext w
  simp only [ActualCovarianceMarkFields.cappedResidual,fullResidualCovariance,Matrix.add_apply,Matrix.sum_apply]
  rfl

end SHE.ControlledThetaCovarianceFields
