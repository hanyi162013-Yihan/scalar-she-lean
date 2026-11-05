module

public import SHE.ControlledThetaNativeMeanHessian
public import SHE.ControlledThetaWeightedFields
public import SHE.ControlledThetaNativeGradient
public import SHE.ProfileReserveTotalMark
public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledThetaNativeAssignments
public import SHE.TwoFreshCompleteWord
public import SHE.ControlledThetaConsistentNative
public import SHE.NativeFirstWholeComplete
public import SHE.NativeFirstOmittedPointwise
public import SHE.ControlledThetaAssigned
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.ControlledThetaNativePointFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal BigOperators
local instance controlledThetaNativePointFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaNativePointFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaNativePointFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

attribute [local irreducible] ActualMeanKernel.cappedAverage ActualMeanKernel.rowPoint

variable {W:Type} [MeasurableSpace W]

/-- Literal original law-q/row-r point kernel under arbitrary joint
substitution of the reference, current mean and history. -/
theorem rowPoint_measurable (k:ℕ)
    (p:W→ℝ×Inputs) (hp:Measurable p) (h:W→History X k) (hh:Measurable h)
    (q r:W→ℝ) (hq:Measurable q) (hr:Measurable r)
    (m:W→WordRecursion.State (n+k)) (hm:Measurable m)
    (y:W→HeatCircle) (hy:Measurable y):
    Measurable (fun w=>ActualMeanKernel.rowPoint (Base (p w)) k (q w) (r w)
      (fun _=>m w) (h w) (y w)):=by
  classical
  classical
  let S:VariableObservations.Family W (n+k):=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  have hmap:Measurable (fun w=>((p w,(q w,h w)),m w)):=
    (hp.prodMk (hq.prodMk hh)).prodMk hm
  have hd:=(ControlledThetaBackwardFields.gradient_joint_measurable P P.coefficient hA Λ v b hvb
    Z htarget hstop F hF hFm k).comp hmap
  have hrow:=VariableWeightedRows.measurable S 0 q r hq hr y hy
  have hev:Continuous (fun z:((WordRecursion.State (n+k)→L[ℝ]ℝ)×WordRecursion.State (n+k))=>z.1 z.2):=
    continuous_fst.clm_apply continuous_snd
  have hv:=hev.measurable.comp (hd.prodMk hrow)
  have ht:Measurable (fun w=>(carrier (Base (p w)) k).terminal (h w)):=by
    have ht0:=(ControlledThetaWordFields.terminal_joint_measurable P P.coefficient hA Λ v b hvb
      Z htarget hstop F hF hFm k).comp (hp.prodMk hh)
    convert! ht0 using 1
  have hset:MeasurableSet {w|q w<(carrier (Base (p w)) k).terminal (h w) ∧
      r w<(carrier (Base (p w)) k).terminal (h w)}:=
    (measurableSet_lt hq ht).inter (measurableSet_lt hr ht)
  have hfield:Measurable (fun w=>if q w<(carrier (Base (p w)) k).terminal (h w) ∧
      r w<(carrier (Base (p w)) k).terminal (h w) then
      fderiv ℝ (ActualMeanKernel.cappedAverage (Base (p w)) k (q w) (h w)) (m w)
        (StopWeightedRows.weightedHeatRow 0 (S.observations w) (q w) (r w) (y w)) else (0:ℝ)):=by
    convert! hv.ite hset (measurable_const (a:=(0:ℝ))) using 1
  convert! hfield using 1
  funext w
  simp only [ActualMeanKernel.rowPoint]
  split_ifs with ha
  · simp only [ActualMeanKernel.cappedAverage,min_eq_left ha.1.le]
    congr 1
    apply PiLp.ext
    intro i
    simp only [StopWeightedRows.weightedHeatRow,StopWeightedRows.diagonal_apply,
      StopWeightedRows.weights,neg_zero,zero_mul,Real.exp_zero,one_mul]
    rfl
  · rfl

/-- Literal original mixed-Hessian mean point. The guard only extends
it beyond its true current window, for joint Borel integration. -/
def meanPoint (p:ℝ×Inputs) (k:ℕ) (h:History X k) (q:ℝ)
    (m V E:WordRecursion.State (n+k)):ℝ:=
  if q<(carrier (Base p) k).terminal h then
    GaussianTaylor.hessian (ActualMeanKernel.cappedAverage (Base p) k q h) m V E else 0

theorem meanPoint_measurable (k:ℕ)
    (p:W→ℝ×Inputs) (hp:Measurable p) (h:W→History X k) (hh:Measurable h)
    (q:W→ℝ) (hq:Measurable q) (m V E:W→WordRecursion.State (n+k))
    (hm:Measurable m) (hV:Measurable V) (hE:Measurable E):
    Measurable (fun w=>meanPoint P hA Λ v b hvb Z htarget hstop F hF hFm (p w) k (h w) (q w)
      (m w) (V w) (E w)):=by
  have hmap:Measurable (fun w=>((p w,(q w,h w)),m w)):=
    (hp.prodMk (hq.prodMk hh)).prodMk hm
  have hH:=(ControlledThetaBackwardFields.hessian_joint_measurable P P.coefficient hA Λ v b hvb
    Z htarget hstop F hF hFm k).comp hmap
  have hevH:Continuous (fun z:((WordRecursion.State (n+k)→L[ℝ]WordRecursion.State (n+k)→L[ℝ]ℝ)×
      WordRecursion.State (n+k))=>z.1 z.2):=continuous_fst.clm_apply continuous_snd
  have hev:Continuous (fun z:((WordRecursion.State (n+k)→L[ℝ]ℝ)×WordRecursion.State (n+k))=>z.1 z.2):=
    continuous_fst.clm_apply continuous_snd
  have hHV:=hevH.measurable.comp (hH.prodMk hV)
  have hHVE:=hev.measurable.comp (hHV.prodMk hE)
  have ht:Measurable (fun w=>(carrier (Base (p w)) k).terminal (h w)):=by
    have ht0:=(ControlledThetaWordFields.terminal_joint_measurable P P.coefficient hA Λ v b hvb
      Z htarget hstop F hF hFm k).comp (hp.prodMk hh)
    convert! ht0 using 1
  unfold meanPoint
  exact hHVE.ite (measurableSet_lt hq ht) (measurable_const (a:=(0:ℝ)))


end SHE.ControlledThetaNativePointFields

