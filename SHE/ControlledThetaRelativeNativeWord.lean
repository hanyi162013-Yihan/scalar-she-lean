module

public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledThetaNativeAssignments
public import SHE.TwoFreshVaryingMoments
public import SHE.NativeFirstOmittedPointwise
public import SHE.ControlledThetaAssigned
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledThetaRelativeNativeWord
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeNativeWord_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeNativeWord_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeNativeWord_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The literal physical TWO-fresh assigned integral is the exact
relative-age fibre used by the genuine random-past conditional moments.
The event is selected once, before theta, past inputs or current mean. -/
theorem assigned_integral_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀(mean:WordRecursion.State (n+k)) (second:Bool) (E V:WordRecursion.State (n+k)) choices,
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      (∫x,twoFreshWord (Base p) (oldProfile P Λ v p.2) k h second Rnative C E V mean choices x
        ∂twoFreshMeasure (Base p) (oldProfile P Λ v p.2) k h Rnative C)=
      TwoFreshFullResidualMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean second
        (directions Zero ((carrier Zero k).observations.observations h) k h) E V
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaTwoFreshArrays.residual_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt mean second E V choices Rnative C
  have hcov:covariances (Base p) ((carrier (Base p) k).observations.observations h)
      (oldProfile P Λ v p.2) k h=
      OldIntervalCovariance.familyCovariance
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (referenceProfile P Λ p.2.1 p.2.2) (fun j=>lower Zero k h j-(v:ℝ))
        (fun j=>upper Zero k h j-(v:ℝ)):=by
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaPhysicalGeometry.covariances_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0))]
    exact ControlledThetaRelativeArrays.old_covariance_relative_fixed
      P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt
  have hres:=hh p q hvq hqt
  change C=_ at hres
  have hnative:Rnative=NativeFirstScoreReserve.covariance P
      (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
      (centers Zero k h) (q-(v:ℝ)):=by
    dsimp only [Rnative]
    rw [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    exact ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q _ _ _
  have hbase:baseline (Base p) k h=(fun j=>ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers Zero k h (leafIndex k (fun i=>i) j)))):=by
    funext j
    rw [ControlledThetaRelativeWord.baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h j,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
  have hdir:directions (Base p) ((carrier (Base p) k).observations.observations h) k h=
      directions Zero ((carrier Zero k).observations.observations h) k h:=by
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    exact ControlledThetaPhysicalGeometry.directions_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) _ k h
  unfold twoFreshWord twoFreshMeasure TwoFreshFullResidualMoments.fibreAverage
  change (∫x,TwoFreshFullResidualMoments.word second _ _ Rnative C E V choices _ _ _ _ _ _ ((),x) ∂_)=_
  rw [hcov,hres,hnative,hbase,hdir]
  rfl

end SHE.ControlledThetaRelativeNativeWord


