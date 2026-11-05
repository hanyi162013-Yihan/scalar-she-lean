module

public import SHE.ControlledFamilyLegFubini
public import SHE.ControlledFamilyProfileMarkFields
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

namespace SHE.ControlledFamilyMeanFieldsBorel
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyMeanFieldsBorel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyMeanFieldsBorel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyMeanFieldsBorel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

/-- Joint Borel measurability of the literal mean leg before any
old-space, old-time, or theta averaging. Every original stopping time
is retained in its damped direction. No profile-derivative hypothesis
is required. -/
theorem mean_variable_measurable
    {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q) (U D : W→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>ControlledFamilyLegFubini.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p w) k (h w) (q w) (U w) (D w) (θ w)) := by
  classical
  let a : W→ℝ×Inputs :=fun w=>(θ w,p w)
  have ha : Measurable a:=hθ.prodMk hp
  let m : W→WordRecursion.State (n+k) :=fun w=>Mean (p w) k (h w) (q w) (U w) (D w) (θ w)
  have hm : Measurable m:=ControlledFamilyFrontFields.mean_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq U D hU hD θ hθ
  have hm1:=ControlledFamilyFrontFields.mean_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq U D hU hD (fun _=>1) measurable_const
  have hm0:=ControlledFamilyFrontFields.mean_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq U D hU hD (fun _=>0) measurable_const
  let d : W→WordRecursion.State (n+k) :=fun w=>PhysicalMeanRange.dampedDirection
    (Sig (p w) k (h w)) (Tar (p w) k (h w)) (Cen (p w) k (h w)) (q w-(v:ℝ)) Λ (D w)
  have hd : Measurable d := by
    convert hm1.sub hm0 using 1
    funext w
    change d w=Mean (p w) k (h w) (q w) (U w) (D w) 1-Mean (p w) k (h w) (q w) (U w) (D w) 0
    rw [←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p w) k (h w) (q w) (U w) (D w) 1,
      ←ControlledFamilyActualTransfer.mean_relative P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p w) k (h w) (q w) (U w) (D w) 0]
    simp only [ControlledJointWeightedWord.jointMeanVector,one_smul,zero_smul,add_zero,add_sub_cancel_left]
    rfl
  have hmap : Measurable (fun w=>((a w,(q w,h w)),m w)):=
    (ha.prodMk (hq.prodMk hh)).prodMk hm
  have hg:=(ControlledThetaBackwardFields.gradient_joint_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k).comp hmap
  have hmean:=(continuous_fst.clm_apply continuous_snd).measurable.comp (hg.prodMk hd)
  let g : W→ℝ :=fun w=>fderiv ℝ
    (ActualMeanKernel.cappedAverage (Base (a w)) k (q w) (h w)) (m w) (d w)
  have hgm : Measurable g:=hmean
  have hT:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
  have hmap0 : Measurable (fun w=>(((0:ℝ),p w),h w)) := (measurable_const.prodMk hp).prodMk hh
  have ht0:=hT.comp hmap0
  have hs : MeasurableSet {w : W | (v:ℝ)≤q w ∧ q w<(carrier (Base (0,p w)) k).terminal (h w)} :=
    (measurableSet_le measurable_const hq).inter (measurableSet_lt hq ht0)
  have hhg : Measurable (fun w=>if (v:ℝ)≤q w ∧ q w<(carrier (Base (0,p w)) k).terminal (h w) then g w else 0) :=
    hgm.ite hs measurable_const
  convert hhg using 1
  funext w
  unfold ControlledFamilyLegFubini.mean
  split_ifs with hb
  · have hqt : q w≤(carrier (Base (θ w,p w)) k).terminal (h w) := by
      rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
        (θ w,p w) (0,p w) k]
      exact hb.2.le
    simp only [g,a,m,d,ActualMeanKernel.cappedAverage,min_eq_left hqt]
  · rfl

end SHE.ControlledFamilyMeanFieldsBorel
