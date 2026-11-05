module

public import SHE.ControlledFamilyMarkedFields
public import SHE.HistoryProductMeasure
public import SHE.ControlledFamilyHistoryTransfer
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

namespace SHE.ControlledFamilyMarkedAverages
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyMarkedAverages_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyMarkedAverages_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyMarkedAverages_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "ActiveMark" => ControlledFamilyHistoryTransfer.activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "ActiveValue" => ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The original old-space average of the entire actual three-leg mark
is jointly Borel in theta/current time/current sample and old times. -/
theorem old_space_average_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (root : W→X) (hroot : Measurable root)
    (t : W→Fin k→ℝ) (ht : Measurable t) (q : W→ℝ) (hq : Measurable q)
    (U D : W→CircleL2) (hU : Measurable U) (hD : Measurable D) (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>∫ x : Fin k→HeatCircle,
      ActiveMark (p w) k (HistoryProductMeasure.separated k (root w,t w,x)) (q w) (U w) (D w) (θ w)
        ∂Measure.pi (fun _=>haarAddCircle)) := by
  have hh : Measurable (fun z : W×(Fin k→HeatCircle)=>HistoryProductMeasure.separated k (root z.1,t z.1,z.2)) :=
    (HistoryProductMeasure.separated_measurable k).comp
      ((hroot.comp measurable_fst).prodMk ((ht.comp measurable_fst).prodMk measurable_snd))
  have hg:=ControlledFamilyMarkedFields.active_mark_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : W×(Fin k→HeatCircle)=>p z.1) (hp.comp measurable_fst) _ hh
    (fun z=>q z.1) (hq.comp measurable_fst) (fun z=>U z.1) (fun z=>D z.1)
    (hU.comp measurable_fst) (hD.comp measurable_fst) (fun z=>θ z.1) (hθ.comp measurable_fst)
  exact (hg.stronglyMeasurable.integral_prod_right' (ν:=Measure.pi (fun _ : Fin k=>haarAddCircle))).measurable

/-- The complete original-history average is genuinely Borel with all
reference data and actual current states. No fixed-reference theorem
is evaluated along a random-profile diagonal. -/
theorem old_history_average_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (ρ : Measure X) [IsFiniteMeasure ρ] {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (q : W→ℝ) (hq : Measurable q)
    (U D : W→CircleL2) (hU : Measurable U) (hD : Measurable D) (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>∫ h : History X k,ActiveMark (p w) k h (q w) (U w) (D w) (θ w)
      ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k) := by
  have hg:=ControlledFamilyMarkedFields.active_mark_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : W×History X k=>p z.1) (hp.comp measurable_fst) Prod.snd measurable_snd
    (fun z=>q z.1) (hq.comp measurable_fst) (fun z=>U z.1) (fun z=>D z.1)
    (hU.comp measurable_fst) (hD.comp measurable_fst) (fun z=>θ z.1) (hθ.comp measurable_fst)
  exact (hg.stronglyMeasurable.integral_prod_right'
    (ν:=historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k)).measurable

end SHE.ControlledFamilyMarkedAverages
