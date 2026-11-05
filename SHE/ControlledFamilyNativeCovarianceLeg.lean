module
public import SHE.ControlledFamilyNativeWordIdentity
public import SHE.ControlledFamilyActualTransfer
public import SHE.ObservationMarkTimeShift
public import SHE.ControlledFamilyResidualIdentity
public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledFamilyThreeLeg
public import SHE.NativeDirectionKernelFTC

public import SHE.ControlledThetaStoppedCovariance
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyNativeCovarianceLeg
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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
local notation "Lo" => ControlledFamilyThreeLeg.lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
open ControlledFamilyThreeLeg

local notation "R"=>ControlledFamilyNativeLegs.reserve P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "C"=>ControlledFamilyNativeLegs.remaining P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Avg"=>ControlledFamilyNativeLegs.average P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mean"=>ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm

def physicalAverage (p:Inputs) (θ:ℝ) (k:ℕ) (h:History X k) (q:ℝ) (E:WordRecursion.State (n+k)):
    WordRecursion.State (n+k)→ℝ:=
    WeightedBorelAverage.average
      ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
        (covariances (Base (θ,p)) ((carrier (Base (θ,p)) k).observations.observations h)
          (oldProfile P Λ v p) k h j))).prod
        (multivariateGaussian 0 (NativeFirstScoreReserve.covariance P
          (stops (Base (θ,p)) k h) (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)))
      (GaussianFixedFirstAverage.weight
        (NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
          (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q) E
        (fun old=>∏j,MeasurableGaussianScores.secondScore
          (covariances (Base (θ,p)) ((carrier (Base (θ,p)) k).observations.observations h)
            (oldProfile P Λ v p) k h j)
          (directions (Base (θ,p)) ((carrier (Base (θ,p)) k).observations.observations h) k h j) (old j)))
      (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base (θ,p)) k h (fun i=>i))

local notation "Phys"=>physicalAverage P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem physicalAverage_eq (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (p:Inputs) (θ:ℝ) (k:ℕ) (h:History X k) (q:ℝ) (E:WordRecursion.State (n+k)):
    Phys p θ k h q E=Avg p k h q E (test Finset.univ (Root p k h) (Leaf k)
      (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)):=
  ControlledFamilyNativeWordIdentity.average_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot p θ k h q E

/-- The covariance component of the native directional FTC is the
original physical signed continuum mark, with the full original
centered recursive word and the same first-score direction. -/
theorem covariance_leg_eq_physical_all_parameters_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀θ q:ℝ,(v:ℝ)≤q→q≤(carrier (Base (0,p)) k).terminal h→
      ∀(U D:CircleL2)(E:WordRecursion.State (n+k)),
      ControlledFamilyNativeLegs.covarianceLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D E θ=
      FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
        (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q-
          NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
            (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)
        (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ)))
        (StoppedGaussianFeatures.stoppedRow (stops (Base (θ,p)) k h) (targets (Base (θ,p)) k h)
          (centers (Base (θ,p)) k h))
        (Phys p θ k h q E) (Mean p k h q U D θ):=by
  filter_upwards [ControlledFamilyNativeWordIdentity.remaining_eq_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hc
  intro p θ q hvq hqt U D E
  have hσ:(fun i=>Sig p k h i+(v:ℝ))=stops (Base (θ,p)) k h:=by
    funext i
    have hh:=congrFun (ControlledFamilyValueIdentity.relative_stops_eq
      P A hA Λ v b hvb Z htarget hstop F hF hFm hroot p θ k h) i
    dsimp only at hh
    linarith
  have hT:(fun i=>Tar p k h i+(v:ℝ))=targets (Base (θ,p)) k h:=by
    funext i
    have hh:=congrFun (ControlledFamilyValueIdentity.relative_targets_eq
      P A hA Λ v b hvb Z htarget hstop F hF hFm p θ k h) i
    dsimp only at hh
    linarith
  have he:=ObservationTimeShift.covarianceMark_translation (v:ℝ) (q-(v:ℝ))
    (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h))
    (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q-
      NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
        (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q)
    (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ))
    (Phys p θ k h q E) (Mean p k h q U D θ)
  rw [sub_add_cancel,hσ,hT,←ControlledFamilyValueIdentity.centers_eq
    P A hA Λ v b hvb Z htarget hstop F hF hFm p θ k h] at he
  rw [hc p θ q hvq hqt,physicalAverage_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot,
    ←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm] at he
  rw [ControlledFamilyValueIdentity.centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm] at he
  rw [hc p θ q hvq hqt,physicalAverage_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot,
    ←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyValueIdentity.centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  exact he.symm

end SHE.ControlledFamilyNativeCovarianceLeg
