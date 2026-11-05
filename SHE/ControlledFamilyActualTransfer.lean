module

public import SHE.ControlledFamilyValueIdentity
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyActualTransfer
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyActualTransfer_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyActualTransfer_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyActualTransfer_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

/-- Relative ages leave both the physical heat age and the original-stop
damping unchanged. -/
theorem jointMean_time_translation {m : ℕ} (σ T : Fin m→ℝ) (c : Fin m→UnitAddCircle)
    (a q Λ : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledJointWeightedWord.jointMeanVector (fun i=>σ i-a) (fun i=>T i-a) c (q-a) Λ U D θ=
      ControlledJointWeightedWord.jointMeanVector σ T c q Λ U D θ := by
  apply PiLp.ext
  intro i
  have hT : (T i-a)-(q-a)=T i-q := by ring
  have hσ : (σ i-a)-(q-a)=σ i-q := by ring
  simp only [ControlledJointWeightedWord.jointMeanVector_apply,hT,hσ]

def mean (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    WordRecursion.State (n+k) :=
  ControlledJointWeightedWord.jointMeanVector
    (fun i=>((carrier (Base (0,p)) k).observations.observations h i).stop)
    (fun i=>((carrier (Base (0,p)) k).observations.observations h i).target)
    (Cen p k h) q Λ U D θ

theorem mean_relative (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h)
      (q-(v:ℝ)) Λ U D θ=mean P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ :=
  jointMean_time_translation _ _ _ (v:ℝ) q Λ U D θ

/-- The actual Gaussian-front recursive test at the literal absolute-age
joint current vector. Both the covariance and every centered leaf move
along the canonical reference interpolation. -/
def actualValue (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  gaussianAverage (WordRecursion.covariance
    (referenceData P A hA Λ θ v b hvb p).reference
    ((carrier (Base (θ,p)) k).observations.observations h) q ((carrier (Base (θ,p)) k).terminal h))
    (UncutSmoothWords.test (Base (θ,p)) k h)
    (mean P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ)

/-- Actual three-leg FTC, simultaneously for ALL original past inputs
and current states on a single original history event. This is the
canonical recursive word itself, with its original stop damping and
full centered baselines, rather than a separately supplied test. -/
theorem actual_transfer_all_parameters_ae (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ q : ℝ,(v:ℝ)≤q → q<(carrier (Base (0,p)) k).terminal h →
      ∀ U D : CircleL2,
      (∀ᵐ θ ∂volume,HasDerivAt
        (actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D)
        (Mark p k h q U D θ) θ) ∧
      ∀ r t,IntervalIntegrable (Mark p k h q U D) volume r t ∧
        (∫ θ in r..t,Mark p k h q U D θ)=
          actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D t-
            actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D r := by
  filter_upwards [ControlledFamilyValueIdentity.value_eq_actual_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k] with h hh
  intro p q hvq hqt U D
  have he : Value p k h q U D=actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D := by
    funext θ
    rw [hh p θ q hvq hqt.le U D,mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm]
    rfl
  have hf:=ControlledFamilyThreeLeg.transfer P A hA Λ v b hvb Z htarget hstop F hF hFm
    hΛ hsmall hroot hspan p k h q hvq hqt U D
  rw [he] at hf
  exact hf

/-- At theta one the absolute-age mean is exactly the original joint
observation, with no common-stop substitution and no zero-age field
premise on the positive current window. -/
theorem mean_one_eq_evaluate
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (p : Inputs) (k : ℕ) (h : History X k) {q : ℝ}
    (hqt : q<(carrier (Base (0,p)) k).terminal h)
    (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ) :
    mean P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q (U q) (V q-U q) 1=
      JointWordObserve.evaluate Λ U V XU XV ((carrier (Base (0,p)) k).observations.observations h) q := by
  have hca:=RecursiveScoreSupport.carrier_ages (Base (0,p)) hages k h
  apply ControlledJointWeightedWord.jointMeanVector_one_eq_evaluate
  · intro i
    exact (hqt.trans_le ((carrier (Base (0,p)) k).stops_after h i)).trans_le (hca i)
  · intro i
    exact NativeHeatSpan.scale_inverse _

end SHE.ControlledFamilyActualTransfer
