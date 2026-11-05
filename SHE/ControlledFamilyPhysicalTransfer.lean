module

public import SHE.ControlledFamilyMeanLeg
public import SHE.ControlledFamilyCovarianceLeg
public import SHE.ControlledFamilyBaselineLeg
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

namespace SHE.ControlledFamilyPhysicalTransfer
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyPhysicalTransfer_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyPhysicalTransfer_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyPhysicalTransfer_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "CovLeg" => ControlledFamilyCovarianceLeg.covarianceLeg P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "MeanLeg" => ControlledFamilyMeanLeg.meanLeg P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "BaseLeg" => ControlledFamilyBaselineLeg.baselineLeg P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "DB" => ControlledFiniteWord.baselineDerivatives P Λ

theorem mark_eq_three_legs (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    Mark p k h q U D θ=CovLeg p k h q U D θ+MeanLeg p k h q U D θ+BaseLeg p k h q U D θ := by
  unfold ControlledFamilyThreeLeg.mark WeightedWordMarking.mark
    ControlledFamilyCovarianceLeg.covarianceLeg ControlledFamilyMeanLeg.meanLeg
    ControlledFamilyBaselineLeg.baselineLeg
  rw [←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ]
  rfl

/-- The actual continuum covariance field, physical current-mean
Fréchet derivative and all erased-leaf baseline fields at the same
canonical recursive family member and the same literal joint mean. -/
def physicalMark (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  ActualCovarianceMarkFields.point (Base (θ,p)) (oldProfile P Λ v p)
    (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ)))
    k q (Mean p k h q U D θ) h+
  fderiv ℝ (gaussianAverage (WordRecursion.covariance
    (referenceData P A hA Λ θ v b hvb p).reference
    ((carrier (Base (θ,p)) k).observations.observations h) q ((carrier (Base (θ,p)) k).terminal h))
    (UncutSmoothWords.test (Base (θ,p)) k h)) (Mean p k h q U D θ)
    (PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D)+
  ActualBaselineMarkFields.point (Base (θ,p)) (oldProfile P Λ v p) k q
    (fun j=>DB p.1 p.2 (LP p k h) j θ) (Mean p k h q U D θ) h

/-- The whole marked family FTC is identified with the actual physical
three-leg fields, on a common history event for ALL original-past
inputs and current states. It retains finite-depth/smooth-coefficient
scope and every actual centered baseline. -/
theorem physical_transfer_all_parameters_ae (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ q : ℝ,(v:ℝ)≤q → q<(carrier (Base (0,p)) k).terminal h →
      ∀ U D : CircleL2,
      (∀ᵐ θ ∂volume,HasDerivAt
        (ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D)
        (physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ) θ) ∧
      ∀ r t,IntervalIntegrable (physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D) volume r t ∧
        (∫ θ in r..t,physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ)=
          ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D t-
            ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D r := by
  filter_upwards [ControlledFamilyActualTransfer.actual_transfer_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan ρ k,
    ControlledFamilyCovarianceLeg.covariance_leg_eq_point_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k,
    ControlledFamilyMeanLeg.mean_leg_eq_fderiv_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hroot ρ k,
    ControlledFamilyBaselineLeg.baseline_leg_eq_point_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hf hc hm hb
  intro p q hvq hqt U D
  have he : Mark p k h q U D=physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D := by
    funext θ
    rw [mark_eq_three_legs P A hA Λ v b hvb Z htarget hstop F hF hFm,
      hc p θ q hvq hqt U D,hm p θ q hvq hqt U D,hb p θ q hvq hqt U D]
    rfl
  have hh:=hf p q hvq hqt U D
  rw [he] at hh
  exact hh

end SHE.ControlledFamilyPhysicalTransfer
