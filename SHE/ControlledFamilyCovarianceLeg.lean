module

public import SHE.ControlledFamilyResidualIdentity
public import SHE.ObservationMarkTimeShift
public import SHE.ActualCovarianceMarkFields
public import SHE.ControlledFamilyActualTransfer
public import SHE.ChainAssignedRepresentation
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyCovarianceLeg
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyCovarianceLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyCovarianceLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyCovarianceLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Value" => ControlledFamilyThreeLeg.value P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFamilyThreeLeg.mark P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Lo" => ControlledFamilyThreeLeg.lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mean" => ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

def covarianceLeg (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  ControlledFixedReserve.mark P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
    (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ))
    (WeightedBorelAverage.average (Law p k h) (Wgt p k h) (fun y=>∑ j,y j)
      (test Finset.univ (Root p k h) (Leaf k)
        (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ))) θ
    (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ)

/-- The literal covariance leg is the actual signed physical continuum
mark with the entire old-averaged word and the original separately
stopped rows. This remains an equality after arbitrary random-past
substitution because its history event is common to every parameter. -/
theorem covariance_leg_eq_point_all_parameters_ae
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ θ q : ℝ,(v:ℝ)≤q → q<(carrier (Base (0,p)) k).terminal h →
      ∀ U D : CircleL2,
      covarianceLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ=
      ActualCovarianceMarkFields.point (Base (θ,p)) (oldProfile P Λ v p)
        (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ)))
        k q (Mean p k h q U D θ) h := by
  filter_upwards [ControlledFamilyResidualIdentity.residual_eq_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hc
  intro p θ q hvq hqt U D
  have hqt' : q<(carrier (Base (θ,p)) k).terminal h := by
    rw [TME (θ,p) (0,p) k]
    exact hqt
  rw [ActualCovarianceMarkFields.point_of_active _ _ _ _ _ _ _ hqt']
  have hσ : (fun i=>Sig p k h i+(v:ℝ))=stops (Base (θ,p)) k h := by
    funext i
    have he:=congrFun (ControlledFamilyValueIdentity.relative_stops_eq
      P A hA Λ v b hvb Z htarget hstop F hF hFm hroot p θ k h) i
    dsimp only at he
    linarith
  have hT : (fun i=>Tar p k h i+(v:ℝ))=targets (Base (θ,p)) k h := by
    funext i
    have he:=congrFun (ControlledFamilyValueIdentity.relative_targets_eq
      P A hA Λ v b hvb Z htarget hstop F hF hFm p θ k h) i
    dsimp only at he
    linarith
  have he:=ObservationTimeShift.covarianceMark_translation (v:ℝ) (q-(v:ℝ))
    (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h))
    (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q)
    (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ))
    (oldAverage (Base (θ,p)) (oldProfile P Λ v p) k h) (Mean p k h q U D θ)
  rw [sub_add_cancel,hσ,hT,←ControlledFamilyValueIdentity.centers_eq
    P A hA Λ v b hvb Z htarget hstop F hF hFm p θ k h] at he
  rw [hc p θ q hvq hqt.le,
    ControlledFamilyWordIdentity.old_average_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm] at he
  rw [ControlledFamilyValueIdentity.centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm] at he
  rw [hc p θ q hvq hqt.le,
    ControlledFamilyWordIdentity.old_average_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyValueIdentity.centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  exact he.symm

end SHE.ControlledFamilyCovarianceLeg
