module

public import SHE.ControlledFamilyResidualIdentity
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

namespace SHE.ControlledFamilyMeanLeg
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyMeanLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyMeanLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyMeanLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

def meanLeg (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  GaussianRangeSmooth.ProfileReserve.affineMeanMark
    (ControlledFixedReserve.covariance P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
      (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)))
    (WeightedBorelAverage.average (Law p k h) (Wgt p k h) (fun y=>∑ j,y j)
      (test Finset.univ (Root p k h) (Leaf k)
        (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)))
    (PhysicalMeanRange.currentDirection (Tar p k h) (Cen p k h) (q-(v:ℝ)) U)
    (PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D) θ

/-- The literal first-score mean leg is exactly the derivative of the
actual canonical recursive Gaussian-front test. The full remaining
covariance supplies the range, even with singular collisions; no range
or conditioning hypothesis is supplied by the caller. -/
theorem mean_leg_eq_fderiv_all_parameters_ae (hΛ : 0≤Λ)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ θ q : ℝ,(v:ℝ)≤q → q<(carrier (Base (0,p)) k).terminal h →
      ∀ U D : CircleL2,
      meanLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ=
      fderiv ℝ (gaussianAverage (WordRecursion.covariance
        (referenceData P A hA Λ θ v b hvb p).reference
        ((carrier (Base (θ,p)) k).observations.observations h) q ((carrier (Base (θ,p)) k).terminal h))
        (UncutSmoothWords.test (Base (θ,p)) k h)) (Mean p k h q U D θ)
        (PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D) := by
  have hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target := by
    intro x i
    rw [hroot x i]
    exact htarget x i
  filter_upwards [ControlledFamilyResidualIdentity.residual_eq_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k,
    ControlledFamilyResidualIdentity.damped_range_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hroot ρ k,
    ControlledThetaSupported.physical_chain_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hc hd hh
  intro p θ q hvq hqt U D
  have hqt' : q<(carrier (Base (θ,p)) k).terminal h := by
    rw [TME (θ,p) (0,p) k]
    exact hqt
  obtain ⟨chain,hs,_,hp⟩:=hh (θ,p)
  have hscore:=full_residual_first_score_of_chain (Base (θ,p)) (oldProfile P Λ v p)
    chain hs hp hages q (v.2.trans hvq) hqt'
  have hm:=ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ
  have he:=hc p θ q hvq hqt.le
  have hd':=hd p θ q hvq hqt D
  have hf:=(hscore.2 _ (Mean p k h q U D θ) hd').symm
  rw [he,ControlledFamilyWordIdentity.old_average_eq P A hA Λ v b hvb Z htarget hstop F hF hFm] at hf
  rw [←hm] at hf
  rw [←hm]
  exact hf

end SHE.ControlledFamilyMeanLeg
