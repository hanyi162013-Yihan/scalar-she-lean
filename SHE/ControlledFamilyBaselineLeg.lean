module

public import SHE.ControlledFamilyResidualIdentity
public import SHE.ControlledFamilyActualTransfer
public import SHE.ActualBaselineMarkFields
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyBaselineLeg
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyBaselineLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyBaselineLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyBaselineLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

theorem average_scaled_root {Y ι : Type*} [MeasurableSpace Y] [DecidableEq ι] {m : ℕ}
    (s : Finset ι) (ν : Measure Y) (w : Y→ℝ) (shift : Y→WordRecursion.State m)
    (C : Matrix (Fin m) (Fin m) ℝ) (R : WordRecursion.State m→ℝ)
    (a : ι→WordRecursion.State m→ℝ) (d : ι→ℝ) (c : ℝ) (z : WordRecursion.State m) :
    gaussianAverage C (WeightedBorelAverage.average ν w shift (test s (fun x=>c*R x) a d)) z=
      c*gaussianAverage C (WeightedBorelAverage.average ν w shift (test s R a d)) z := by
  have he : test s (fun x=>c*R x) a d=(fun x=>c*test s R a d x) := by
    funext x
    unfold test
    ring
  rw [he]
  unfold gaussianAverage
  simp_rw [WeightedBorelAverage.const_mul]
  exact integral_const_mul _ _

def baselineLeg (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  -(∑ j : Fin k,ControlledFiniteWord.baselineDerivatives P Λ p.1 p.2 (LP p k h) j θ*
    gaussianAverage
      (ControlledFixedReserve.covariance P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
        (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)) θ)
      (WeightedBorelAverage.average (Law p k h) (Wgt p k h) (fun y=>∑ j,y j)
        (test (Finset.univ.erase j) (Root p k h) (Leaf k)
          (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)))
      (Mean p k h q U D θ))

/-- The full baseline leg is exactly the physical erased-leaf mark with
its original (1/2)^k normalization. Every baseline derivative remains,
and the SAME old scores and full remaining Gaussian are used. -/
theorem baseline_leg_eq_point_all_parameters_ae
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ θ q : ℝ,(v:ℝ)≤q → q<(carrier (Base (0,p)) k).terminal h →
      ∀ U D : CircleL2,
      baselineLeg P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ=
      ActualBaselineMarkFields.point (Base (θ,p)) (oldProfile P Λ v p) k q
        (fun j=>ControlledFiniteWord.baselineDerivatives P Λ p.1 p.2 (LP p k h) j θ)
        (Mean p k h q U D θ) h := by
  filter_upwards [ControlledFamilyResidualIdentity.residual_eq_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hc
  intro p θ q hvq hqt U D
  have hqt' : q<(carrier (Base (θ,p)) k).terminal h := by
    rw [TME (θ,p) (0,p) k]
    exact hqt
  rw [ActualBaselineMarkFields.point_of_active _ _ _ _ _ _ _ hqt']
  unfold baselineLeg baselineMark
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold omittedAverage
  rw [hc p θ q hvq hqt.le,
    ControlledFamilyWordIdentity.old_matrices_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyWordIdentity.old_directions_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyWordIdentity.baseline_eq P A hA Λ v b hvb Z htarget hstop F hF hFm]
  exact average_scaled_root (Finset.univ.erase j) (Law p k h) (Wgt p k h) (fun y=>∑ j,y j) _
    (initial (Base (0,p)) k h (fun i=>i)) (Leaf k) _ ((1/2:ℝ)^k) _

end SHE.ControlledFamilyBaselineLeg
