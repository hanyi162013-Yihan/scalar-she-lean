module

public import SHE.ControlledReferenceThetaGeometry
public import SHE.ActualMeanKernelJoint
public import SHE.ControlledProfileFamilies

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

/-! Joint Borel fields of the actual interpolation-dependent recursive
words. The profile, every Gaussian covariance and every centered leaf
varies with theta; a fixed-level measurability theorem is not substituted
for this parameter induction. -/
namespace SHE.ControlledThetaWordFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
  SmoothCylinders UniformSmooth NormalizedInsertion GaussianContinuity
open scoped NNReal
local instance controlledThetaWordFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaWordFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaWordFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "NME" => ControlledReferenceThetaGeometry.carrier_nodeTime_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "RME" => ControlledReferenceThetaGeometry.row_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "WME" => ControlledReferenceThetaGeometry.weight_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Actual canonical coefficient, jointly in theta, both past states,
and physical space-time. -/
theorem coefficient_joint_measurable : Measurable (fun p : (ℝ×Inputs)×(ℝ×HeatCircle)=>
    ControlledReferenceWindows.coefficient P Λ p.1.1 v p.1.2 p.2) := by
  have hm:=ControlledProfile.profile_joint_measurable P Λ
  have hmap : Measurable (fun p : (ℝ×Inputs)×(ℝ×HeatCircle)=>
      ((p.1.2,p.1.1),(p.2.1-(v:ℝ),p.2.2))) :=
    (measurable_fst.snd.prodMk measurable_fst.fst).prodMk
      ((measurable_snd.fst.sub_const (v:ℝ)).prodMk measurable_snd.snd)
  have hh:=hm.comp hmap
  convert hh using 1
  rfl

theorem terminal_joint_measurable (k : ℕ) :
    Measurable (fun p : (ℝ×Inputs)×History X k=>(carrier (Base p.1) k).terminal p.2) := by
  convert ((carrier (Base (0,(0,0))) k).terminal_measurable).comp measurable_snd using 1
  funext p
  exact TME p.1 (0,(0,0)) k p.2

theorem nodeTime_joint_measurable (k : ℕ) :
    Measurable (fun p : (ℝ×Inputs)×History X (k+1)=>(carrier (Base p.1) k).nodeTime p.2) := by
  convert ((carrier (Base (0,(0,0))) k).nodeTime_measurable).comp measurable_snd using 1
  funext p
  exact NME p.1 (0,(0,0)) k p.2

/-- The actual carrier observations, with the reference parameters in
their measurable parameter space. -/
def carrierFamily (k : ℕ) : VariableObservations.Family ((ℝ×Inputs)×History X k) (n+k) where
  observations p:=(carrier (Base p.1) k).observations.observations p.2
  stop_measurable i:=by
    convert ((carrier (Base (0,(0,0))) k).observations.stop_measurable i).comp measurable_snd using 1
    funext p
    rw [OME p.1 (0,(0,0)) k p.2]
    rfl
  target_measurable i:=by
    convert ((carrier (Base (0,(0,0))) k).observations.target_measurable i).comp measurable_snd using 1
    funext p
    rw [OME p.1 (0,(0,0)) k p.2]
    rfl
  center_measurable i:=by
    convert ((carrier (Base (0,(0,0))) k).observations.center_measurable i).comp measurable_snd using 1
    funext p
    rw [OME p.1 (0,(0,0)) k p.2]
    rfl

/-- Every node covariance in the genuine theta-dependent recursion is
jointly Borel, including changing ranks. -/
theorem nodeCovariance_joint_measurable (k : ℕ) :
    Measurable (fun p : (ℝ×Inputs)×History X (k+1)=>(carrier (Base p.1) k).nodeCovariance p.2) := by
  let Ξ:=(ℝ×Inputs)×History X (k+1)
  let S : VariableObservations.Family Ξ (n+k) := CutoffWordLevel.reindexFamily
    (carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun p : Ξ=>(p.1,p.2.1)) (measurable_fst.prodMk measurable_snd.fst)
  have hc : Measurable (fun p : Ξ×(ℝ×HeatCircle)=>
      ControlledReferenceWindows.coefficient P Λ p.1.1.1 v p.1.1.2 p.2) := by
    have hm:=coefficient_joint_measurable P Λ v
    have hmap : Measurable (fun p : Ξ×(ℝ×HeatCircle)=>(p.1.1,p.2)) :=
      measurable_fst.fst.prodMk measurable_snd
    have hh:=hm.comp hmap
    exact hh
  have ht : Measurable (fun p : Ξ=>(carrier (Base p.1) k).terminal p.2.1) := by
    have hm:=terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    have hmap : Measurable (fun p : Ξ=>(p.1,p.2.1)) := measurable_fst.prodMk measurable_snd.fst
    have hh:=hm.comp hmap
    exact hh
  have hq:=nodeTime_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
  have hh:=S.positive_covariance_measurable hc hq ht
    (fun p=>((carrier (Base p.1) k).nodeTime_mem p.2).2)
    (fun p=>((carrier (Base p.1) k).nodeCovariance p.2).property)
  convert hh using 1
  funext p
  apply Subtype.ext
  rfl

/-- All smooth state derivatives of normalized words are uniform over
theta and both original reference inputs at each fixed depth. -/
theorem normalized_uniform (k : ℕ) : UniformBoundedSmooth
    (fun p : (ℝ×Inputs)×History X k=>UncutSmoothWords.normalized (Base p.1) k p.2) := by
  induction k with
  | zero => exact uniform_reindex hF Prod.snd
  | succ k ih =>
    let Q:=(ℝ×Inputs)×History X (k+1)
    have hG := (uniform_reindex ih (fun p : Q=>(p.1,p.2.1))).average
      (fun p : Q=>multivariateGaussian (0 : WordRecursion.State (n+k))
        ((carrier (Base p.1) k).nodeCovariance p.2).val) (fun _=>inferInstance)
    exact core_uniform hA hG
      (fun p : Q=>ControlledReferenceWindows.coefficient P Λ p.1.1 v p.1.2
        ((carrier (Base p.1) k).nodeTime p.2,p.2.2.2))
      (fun p : Q=>unitRow (row (Base p.1) k p.2)) P.upper_nonneg
      (fun p=>ControlledReferenceWindows.coefficient_abs_bound P Λ p.1.1 v p.1.2 _)
      zero_le_one (fun p=>norm_unitRow_le _)

/-- Genuine Borel induction across the interpolation parameter, the
random reference data and all original physical histories. -/
theorem normalized_joint_measurable (k : ℕ) : Measurable
    (fun p : ((ℝ×Inputs)×History X k)×WordRecursion.State (n+k)=>
      UncutSmoothWords.normalized (Base p.1.1) k p.1.2 p.2) := by
  induction k with
  | zero => exact hFm.comp (measurable_fst.snd.prodMk measurable_snd)
  | succ k ih =>
    let Q:=(ℝ×Inputs)×History X (k+1)
    have hFn : Measurable (fun p : Q×WordRecursion.State (n+k)=>
        UncutSmoothWords.normalized (Base p.1.1) k p.1.2.1 p.2) := by
      have hmap : Measurable (fun p : Q×WordRecursion.State (n+k)=>((p.1.1,p.1.2.1),p.2)) :=
        (measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd
      have hh:=ih.comp hmap
      exact hh
    have hG := MeasurableWords.gaussian_average_measurable
      (nodeCovariance_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k)
      hFn (fun p=>((UncutSmoothWords.normalized_uniform (Base p.1) k).smooth p.2.1).continuous)
    have hr : Measurable (fun p : Q=>unitRow (row (Base p.1) k p.2)) := by
      convert (measurable_unitRow.comp (row_measurable (Base (0,(0,0))) k)).comp measurable_snd using 1
      funext p
      rw [RME p.1 (0,(0,0)) k p.2]
      rfl
    have hc := (coefficient_joint_measurable P Λ v).comp
      (measurable_fst.prodMk ((nodeTime_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k).prodMk
        measurable_snd.snd.snd))
    exact core_measurable hA.smooth.continuous.measurable hc hr hG
      (fun p=>((uniform_reindex (normalized_uniform P A hA Λ v b hvb Z htarget hstop F hF hFm k)
        (fun p : Q=>(p.1,p.2.1))).average
        (fun p : Q=>multivariateGaussian (0 : WordRecursion.State (n+k))
          ((carrier (Base p.1) k).nodeCovariance p.2).val) (fun _=>inferInstance)).smooth p |>.of_le (by simp))

theorem test_joint_measurable (k : ℕ) : Measurable
    (fun p : ((ℝ×Inputs)×History X k)×WordRecursion.State (n+k)=>
      UncutSmoothWords.test (Base p.1.1) k p.1.2 p.2) := by
  have hw : Measurable (fun p : (ℝ×Inputs)×History X k=>UncutSmoothWords.weight (Base p.1) k p.2) := by
    convert (UncutSmoothWords.weight_measurable (Base (0,(0,0))) k).comp measurable_snd using 1
    funext p
    exact WME p.1 (0,(0,0)) k p.2
  have hh:= (hw.comp measurable_fst).smul
    (normalized_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k)
  convert hh using 1
  funext p
  exact congrFun (UncutSmoothWords.test_eq_weight_normalized (Base p.1.1) k p.1.2) p.2

end SHE.ControlledThetaWordFields
