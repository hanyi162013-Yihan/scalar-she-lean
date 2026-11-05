module

public import SHE.ControlledFamilyThetaFubini
public import SHE.ThreePieceProductIntegral
public import SHE.ControlledFamilyFrontFields
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyLegFubini
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyLegFubini_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyLegFubini_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyLegFubini_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "Active" => ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Physical" => ControlledFamilyPhysicalTransfer.physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "R₀" => referenceData P A hA Λ 0 v b hvb (0,0)

local notation "ActiveMark" => ControlledFamilyHistoryTransfer.activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Mean"=>ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP"=>ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The literal continuum-covariance leg, restricted to the SAME
original history/current window as the full marked FTC. -/
def covariance (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ:=
  if (v:ℝ)≤q ∧ q<(carrier (Base (0,p)) k).terminal h then
    ActualCovarianceMarkFields.point (Base (θ,p)) (oldProfile P Λ v p)
      (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.derivative P Λ p.1 p.2 (z,θ)))
      k q (Mean p k h q U D θ) h else 0

/-- The literal current-mean derivative, before old-space or old-time
cancellation. The direction retains every original stopping time. -/
def mean (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ:=
  if (v:ℝ)≤q ∧ q<(carrier (Base (0,p)) k).terminal h then
    fderiv ℝ (gaussianAverage (WordRecursion.covariance
      (referenceData P A hA Λ θ v b hvb p).reference
      ((carrier (Base (θ,p)) k).observations.observations h) q ((carrier (Base (θ,p)) k).terminal h))
      (UncutSmoothWords.test (Base (θ,p)) k h)) (Mean p k h q U D θ)
      (PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D) else 0

/-- The full erased-baseline leg, including its negative sign and the
original word normalization. No baseline derivative is omitted. -/
def baseline (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ:=
  if (v:ℝ)≤q ∧ q<(carrier (Base (0,p)) k).terminal h then
    ActualBaselineMarkFields.point (Base (θ,p)) (oldProfile P Λ v p) k q
      (fun j=>ControlledFiniteWord.baselineDerivatives P Λ p.1 p.2 (LP p k h) j θ)
      (Mean p k h q U D θ) h else 0

local notation "Cov"=>covariance P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "MeanLeg"=>mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "BaseLeg"=>baseline P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem active_mark_eq (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) :
    ActiveMark p k h q U D θ=Cov p k h q U D θ+MeanLeg p k h q U D θ+BaseLeg p k h q U D θ := by
  unfold ControlledFamilyHistoryTransfer.activeMark covariance mean baseline
  split_ifs <;> simp only [ControlledFamilyPhysicalTransfer.physicalMark,add_zero]

/-- Genuine absolute product integrability of the whole marked field
from the three actual absolute L¹ section budgets. The theta envelopes
may be nonconstant; only their ordinary scalar integrability is needed.
All moving-reference joint Borel applicability is already discharged. -/
theorem product_integrable_of_leg_budgets (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : Ω→Inputs) (hp : Measurable p) (q : Ω→ℝ) (hq : Measurable q)
    (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (Ec Em Eb : ℝ→ℝ)
    (hEc : IntervalIntegrable Ec volume 0 1) (hEm : IntervalIntegrable Em volume 0 1)
    (hEb : IntervalIntegrable Eb volume 0 1)
    (hC : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>Cov (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
        (μ.prod (historyMeasure R₀ ρ k)) ∧
      (∫ z : Ω×History X k,|Cov (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ|
        ∂μ.prod (historyMeasure R₀ ρ k))≤Ec θ)
    (hM : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>MeanLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
        (μ.prod (historyMeasure R₀ ρ k)) ∧
      (∫ z : Ω×History X k,|MeanLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ|
        ∂μ.prod (historyMeasure R₀ ρ k))≤Em θ)
    (hB : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>BaseLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
        (μ.prod (historyMeasure R₀ ρ k)) ∧
      (∫ z : Ω×History X k,|BaseLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ|
        ∂μ.prod (historyMeasure R₀ ρ k))≤Eb θ) :
    Integrable (fun z : ℝ×(Ω×History X k)=>
      ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (μ.prod (historyMeasure R₀ ρ k))) ∧
    (∫ z : ℝ×(Ω×History X k),
      |ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1|
      ∂(volume.restrict (Ioc (0:ℝ) 1)).prod (μ.prod (historyMeasure R₀ ρ k)))≤
      ∫ θ in (0:ℝ)..1,Ec θ+Em θ+Eb θ := by
  have hFm':=ControlledFamilyMarkedFields.active_mark_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : ℝ×(Ω×History X k)=>p z.2.1) (hp.comp measurable_snd.fst)
    (fun z=>z.2.2) measurable_snd.snd (fun z=>q z.2.1) (hq.comp measurable_snd.fst)
    (fun z=>U z.2.1) (fun z=>D z.2.1) (hU.comp measurable_snd.fst) (hD.comp measurable_snd.fst)
    Prod.fst measurable_fst
  have hec:Integrable Ec (volume.restrict (Ioc (0:ℝ) 1)):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp hEc
  have hem:Integrable Em (volume.restrict (Ioc (0:ℝ) 1)):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp hEm
  have heb:Integrable Eb (volume.restrict (Ioc (0:ℝ) 1)):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp hEb
  have hi:=ThreePieceProductIntegral.integrable
    (volume.restrict (Ioc (0:ℝ) 1)) (μ.prod (historyMeasure R₀ ρ k))
    (fun z : ℝ×(Ω×History X k)=>ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
    (fun z=>Cov (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
    (fun z=>MeanLeg (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
    (fun z=>BaseLeg (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
    hFm' (fun z=>active_mark_eq P A hA Λ v b hvb Z htarget hstop F hF hFm _ _ _ _ _ _ _)
    Ec Em Eb hec hem heb hC hM hB
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hi

end SHE.ControlledFamilyLegFubini
