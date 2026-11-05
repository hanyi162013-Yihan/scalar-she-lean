module

public import SHE.ControlledFamilyPhysicalTransfer
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

namespace SHE.ControlledFamilyHistoryTransfer
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyHistoryTransfer_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyHistoryTransfer_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyHistoryTransfer_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

def activeMark (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  if (v:ℝ)≤q ∧ q<(carrier (Base (0,p)) k).terminal h then Physical p k h q U D θ else 0

/-- The genuine old-history endpoint is integrable for arbitrary
measurably history-dependent past inputs and current states. The bound
comes from the actual normalized recursive words and integrated heat
history mass, not from an assumed word majorant. -/
theorem active_value_integrable (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : History X k→Inputs) (hp : Measurable p) (q : History X k→ℝ) (hq : Measurable q)
    (U D : History X k→CircleL2) (hU : Measurable U) (hD : Measurable D) (θ : ℝ) :
    Integrable (fun h=>Active (p h) k h (q h) (U h) (D h) θ) (historyMeasure R₀ ρ k) := by
  obtain ⟨K,hKn,hK⟩:=ControlledFamilyFrontFields.actual_value_bound P A hA Λ v b hvb
    Z htarget hstop F hF hFm k
  have hm:=ControlledFamilyFrontFields.active_value_measurable P A hA Λ v b hvb
    Z htarget hstop F hF hFm k p hp id measurable_id q hq U D hU hD (fun _=>θ) measurable_const
  have hi:=(UncutHistoryMass.weight_integrable (Base (0,(0,0))) ρ k).const_mul K
  apply hi.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro h
  simp only [Real.norm_eq_abs]
  unfold ControlledFamilyFrontFields.activeValue
  split_ifs with ha
  · exact hK (p h) θ h (q h) (U h) (D h)
  · exact abs_zero.le.trans (mul_nonneg hKn (UncutSmoothWords.weight_nonneg _ _ _))

/-- Actual fixed-depth old-history averaging of the three-leg FTC.
The inner interpolation integral is integrable in the ORIGINAL history
measure, and its integral is the difference of two integrable actual
recursive endpoints. No change of integration order is asserted here. -/
theorem history_integrated_transfer (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : History X k→Inputs) (hp : Measurable p) (q : History X k→ℝ) (hq : Measurable q)
    (U D : History X k→CircleL2) (hU : Measurable U) (hD : Measurable D) (r t : ℝ) :
    Integrable (fun h=>∫ θ in r..t,activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p h) k h (q h) (U h) (D h) θ) (historyMeasure R₀ ρ k) ∧
    (∫ h,(∫ θ in r..t,activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p h) k h (q h) (U h) (D h) θ) ∂historyMeasure R₀ ρ k)=
      (∫ h,Active (p h) k h (q h) (U h) (D h) t ∂historyMeasure R₀ ρ k)-
        (∫ h,Active (p h) k h (q h) (U h) (D h) r ∂historyMeasure R₀ ρ k) := by
  have ht:=active_value_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm ρ k p hp q hq U D hU hD t
  have hr:=active_value_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm ρ k p hp q hq U D hU hD r
  have he : (fun h=>∫ θ in r..t,activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p h) k h (q h) (U h) (D h) θ)=ᵐ[historyMeasure R₀ ρ k]
      fun h=>Active (p h) k h (q h) (U h) (D h) t-Active (p h) k h (q h) (U h) (D h) r := by
    filter_upwards [ControlledFamilyPhysicalTransfer.physical_transfer_all_parameters_ae
      P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan ρ k] with h hh
    by_cases ha : (v:ℝ)≤q h ∧ q h<(carrier (Base (0,p h)) k).terminal h
    · have hf:=(hh (p h) (q h) ha.1 ha.2 (U h) (D h)).2 r t
      simp only [activeMark,ControlledFamilyFrontFields.activeValue,ite_eq_left ha]
      exact hf.2
    · simp only [activeMark,ControlledFamilyFrontFields.activeValue,ite_eq_right ha,intervalIntegral.integral_zero,sub_self]
  refine ⟨(ht.sub hr).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_sub ht hr]

end SHE.ControlledFamilyHistoryTransfer
