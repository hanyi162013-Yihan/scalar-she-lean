module

public import SHE.ControlledFamilyActualTransfer
public import SHE.CarrierNativeObservations
public import SHE.UncutWordEvaluation
public import SHE.JointUncutWordEvaluation
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyReferenceAtPast
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyReferenceAtPast_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyReferenceAtPast_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyReferenceAtPast_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "Mean" => ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- At the original past the physical Gaussian front is exactly the
recursive node Gaussian law used by the finite uncut reference tree. -/
theorem value_at_past_eq_node_average (p : Inputs) (k : ℕ) (h : History X k)
    (U D : CircleL2) (θ : ℝ) :
    ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h v U D θ=
      GaussianSmooth.average (multivariateGaussian 0
        ((carrier (Base (θ,p)) k).nodeCovariance (h,((v:ℝ),0))).val)
        (UncutSmoothWords.test (Base (θ,p)) k h)
        (ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm p k h v U D θ) := by
  have hn : (carrier (Base (θ,p)) k).nodeTime (h,((v:ℝ),0))=(v:ℝ) := by
    unfold CutoffWordLevel.Level.nodeTime ClippedCovariance.clip
    change max (v:ℝ) (min ((carrier (Base (θ,p)) k).terminal h) (v:ℝ))=(v:ℝ)
    have hb : (v:ℝ)≤(carrier (Base (θ,p)) k).terminal h:=(carrier (Base (θ,p)) k).terminal_base h
    rw [min_eq_right hb,max_self]
  have hc : ((carrier (Base (θ,p)) k).nodeCovariance (h,((v:ℝ),0))).val=
      WordRecursion.covariance (referenceData P A hA Λ θ v b hvb p).reference
        ((carrier (Base (θ,p)) k).observations.observations h) v ((carrier (Base (θ,p)) k).terminal h) := by
    change WordRecursion.covariance _ _ ((carrier (Base (θ,p)) k).nodeTime (h,((v:ℝ),0))) _=_
    rw [hn]
  change gaussianAverage _ _ _=gaussianAverage _ _ _
  rw [hc]


/-- The zero interpolation mean is the ordinary heat initial mean,
whereas theta one retains the original-stop controlled correction. -/
theorem mean_zero_eq_initialMean (p : Inputs) (k : ℕ) (h : History X k) (U D : CircleL2) :
    ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm p k h v U D 0=
      CanonicalConditional.initialMean ((carrier (Base (0,p)) k).observations.observations h) v U := by
  apply PiLp.ext
  intro i
  unfold ControlledFamilyActualTransfer.mean
  rw [ControlledJointWeightedWord.jointMeanVector_apply]
  unfold ControlledFamilyThreeLeg.center StoppedGaussianScore.nativeCenter CanonicalConditional.initialMean
  rw [NativeHeatSpan.scale_inverse]
  simp only [zero_mul,add_zero]

/-- The theta-zero endpoint is the uncontrolled Gaussian reference of
this same actual recursive word. It is not the full-D joint state at
zero interpolation. -/
theorem value_zero_at_past_eq_reference (p : Inputs) (k : ℕ) (h : History X k) (U D : CircleL2) :
    ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h v U D 0=
      UncutWordEvaluation.reference (Base (0,p)) U k h := by
  rw [value_at_past_eq_node_average P A hA Λ v b hvb Z htarget hstop F hF hFm,
    mean_zero_eq_initialMean P A hA Λ v b hvb Z htarget hstop F hF hFm]
  rfl

end SHE.ControlledFamilyReferenceAtPast
