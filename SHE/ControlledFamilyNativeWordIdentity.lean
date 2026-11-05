module
public import SHE.ControlledFamilyNativeLegs
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

namespace SHE.ControlledFamilyNativeWordIdentity
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

theorem reserve_eq (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (p:Inputs) (θ:ℝ) (k:ℕ) (h:History X k) (q:ℝ):
    NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h) (targets (Base (θ,p)) k h)
      (centers (Base (θ,p)) k h) q=R p k h q:=by
  rw [ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q,
    ControlledFamilyValueIdentity.relative_stops_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot,
    ControlledFamilyValueIdentity.relative_targets_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyValueIdentity.centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  rfl

/-- The native average is exactly the original centered recursive word,
with its old score law and its independent first score. -/
theorem average_eq (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (p:Inputs) (θ:ℝ) (k:ℕ) (h:History X k) (q:ℝ) (E:WordRecursion.State (n+k)):
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
      (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base (θ,p)) k h (fun i=>i))=
    Avg p k h q E (test Finset.univ (Root p k h) (Leaf k)
      (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)):=by
  rw [ControlledFamilyWordIdentity.old_matrices_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyWordIdentity.old_directions_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyWordIdentity.word_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    reserve_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot]
  rfl

theorem remaining_eq_all_parameters_ae
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:Inputs,∀θ q:ℝ,(v:ℝ)≤q→q≤(carrier (Base (0,p)) k).terminal h→
      fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q-
        NativeFirstScoreReserve.covariance P (stops (Base (θ,p)) k h)
          (targets (Base (θ,p)) k h) (centers (Base (θ,p)) k h) q=C p k h q θ:=by
  filter_upwards [ControlledFamilyResidualIdentity.residual_eq_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hh
  intro p θ q hvq hqt
  rw [hh p θ q hvq hqt,reserve_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot]
  apply ControlledThetaTwoFreshArrays.covariance_sub_native P Λ p.1 p.2 _
    (fixedProfile_measurable P Λ _ _ _ _)
    (fixedProfile_bounds P Λ _ _ _ _ (RelativeHistoryGeometry.relative_disjoint (Base (0,p)) k h))
  intro i
  rw [←ControlledFamilyValueIdentity.relative_stops_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot p 0 k h,
    ←ControlledFamilyValueIdentity.relative_targets_eq P A hA Λ v b hvb Z htarget hstop F hF hFm p 0 k h]
  apply sub_le_sub_right
  exact (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages (Base (0,p))
    (fun x i=>by change (Z.observations x i).stop≤(Z.observations x i).target;rw [hroot x i];exact htarget x i) k h i)

end SHE.ControlledFamilyNativeWordIdentity
