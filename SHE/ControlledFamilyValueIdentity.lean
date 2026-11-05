module

public import SHE.ControlledFamilyWordIdentity
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyValueIdentity
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyValueIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyValueIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyValueIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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
local notation "Value" => ControlledFamilyThreeLeg.value P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem relative_stops_eq (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    (fun i=>stops (Base (θ,p)) k h i-(v:ℝ))=Sig p k h := by
  funext i
  unfold stops ControlledFamilyThreeLeg.sigma
  rw [min_eq_left (CarrierStopBounds.stop_le_initial (Base (θ,p))
    (fun x i=>by change (Z.observations x i).stop≤(b:ℝ);rw [hroot x i]) k h i),OME (θ,p) (0,p) k]

theorem relative_targets_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    (fun i=>targets (Base (θ,p)) k h i-(v:ℝ))=Tar p k h := by
  unfold targets ControlledFamilyThreeLeg.target
  rw [OME (θ,p) (0,p) k]

theorem centers_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    centers (Base (θ,p)) k h=StoppedGaussianScore.nativeCenter (Cen p k h) := by
  funext i
  unfold centers ControlledFamilyThreeLeg.center StoppedGaussianScore.nativeCenter
  rw [OME (θ,p) (0,p) k,NativeHeatSpan.scale_inverse]

theorem relative_lower_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    (fun j=>lower (Base (θ,p)) k h j-(v:ℝ))=Lo p k h := by
  rw [ControlledThetaPhysicalGeometry.lower_eq P A hA Λ v b hvb Z htarget hstop F hF hFm (θ,p) (0,p) k h]
  rfl

theorem relative_upper_eq (p : Inputs) (θ : ℝ) (k : ℕ) (h : History X k) :
    (fun j=>upper (Base (θ,p)) k h j-(v:ℝ))=Hi p k h := by
  rw [ControlledThetaPhysicalGeometry.upper_eq P A hA Λ v b hvb Z htarget hstop F hF hFm (θ,p) (0,p) k h]
  rfl

/-- The exact recursively generated Gaussian-front value, with every
original centered leaf, is the fixed-old three-leg interpolation value.
ONE history event works simultaneously for every past input and theta. -/
theorem value_eq_actual_all_parameters_ae
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ θ q : ℝ,(v:ℝ)≤q → q≤(carrier (Base (0,p)) k).terminal h →
      ∀ U D : CircleL2,
      Value p k h q U D θ=
      gaussianAverage (WordRecursion.covariance
        (referenceData P A hA Λ θ v b hvb p).reference
        ((carrier (Base (θ,p)) k).observations.observations h) q ((carrier (Base (θ,p)) k).terminal h))
        (UncutSmoothWords.test (Base (θ,p)) k h)
        (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h)
          (q-(v:ℝ)) Λ U D θ) := by
  have hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target := by
    intro x i
    rw [hroot x i]
    exact htarget x i
  filter_upwards [ControlledThetaStoppedCovariance.relative_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaSupported.full_residual_average_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hcov hav
  intro p θ q hvq hqt U D
  have hq : 0≤q:=v.2.trans hvq
  have hqt' : q≤(carrier (Base (θ,p)) k).terminal h := by
    rw [TME (θ,p) (0,p) k]
    exact hqt
  have he:=hcov (θ,p) q hq hqt'
  rw [relative_stops_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot,
    relative_targets_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    relative_lower_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    relative_upper_eq P A hA Λ v b hvb Z htarget hstop F hF hFm] at he
  unfold ControlledFamilyThreeLeg.value
  rw [←he,←ControlledFamilyWordIdentity.old_average_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  exact (hav (θ,p) q hq hqt' _).symm

end SHE.ControlledFamilyValueIdentity
