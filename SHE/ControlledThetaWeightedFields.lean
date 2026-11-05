module

public import SHE.ControlledThetaBackwardFields
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHE.VariableWeightedRows
open Set MeasureTheory StoppedFourier WordRecursion StopWeightedRows
local instance variableWeightedRows_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] {N : ℕ}

/-- Variable original stops, independent law/heat-row times and physical
centers all enter one jointly Borel stop-weighted heat row. -/
theorem measurable (Z : VariableObservations.Family W N) (Λ : ℝ)
    (q r : W→ℝ) (hq : Measurable q) (hr : Measurable r)
    (y : W→HeatCircle) (hy : Measurable y) :
    Measurable (fun w=>weightedHeatRow Λ (Z.observations w) (q w) (r w) (y w)) := by
  have hrow:=Z.heatRow_measurable.comp (measurable_id.prodMk (hr.prodMk hy))
  apply (WithLp.measurable_toLp 2 (Fin N→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hw : Measurable (fun w=>weights Λ (Z.observations w) (q w) i) :=
    Real.measurable_exp.comp (((Z.stop_measurable i).sub hq).const_mul (-Λ))
  have hi:=hw.mul ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 (Fin N→ℝ)).comp hrow))
  convert hi using 1
  funext w
  exact diagonal_apply _ _ i

end SHE.VariableWeightedRows

namespace SHE.ControlledThetaWeightedFields
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
  HistoryProductMeasure StopWeightedRows
open scoped NNReal
local instance controlledThetaWeightedFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaWeightedFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaWeightedFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] ActualMeanKernel.cappedAverage ActualMeanKernel.weightedPoint
variable {W : Type} [MeasurableSpace W]

/-- Arbitrary measurable substitution into the literal weighted point
field of the entire moving reference family. The law stays at q, the
physical row stays at r, and every stop-dependent weight stays at q. -/
theorem weightedPoint_measurable (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q r : W→ℝ) (hq : Measurable q) (hr : Measurable r)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m)
    (y : W→HeatCircle) (hy : Measurable y) :
    Measurable (fun w=>ActualMeanKernel.weightedPoint (Base (p w)) k Λ (q w) (r w)
      (fun _=>m w) (h w) (y w)) := by
  classical
  let S : VariableObservations.Family W (n+k):=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  have hmap : Measurable (fun w=>((p w,(q w,h w)),m w)):=
    (hp.prodMk (hq.prodMk hh)).prodMk hm
  have hd:=(ControlledThetaBackwardFields.gradient_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k).comp hmap
  have hrow:=VariableWeightedRows.measurable S Λ q r hq hr y hy
  have hv:=(continuous_fst.clm_apply continuous_snd).measurable.comp (hd.prodMk hrow)
  have ht : Measurable (fun w=>(carrier (Base (p w)) k).terminal (h w)) := by
    have ha:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    have hb:=ha.comp (hp.prodMk hh)
    exact hb
  have hs : MeasurableSet {w | q w<(carrier (Base (p w)) k).terminal (h w) ∧
      r w<(carrier (Base (p w)) k).terminal (h w)}:=
    (measurableSet_lt hq ht).inter (measurableSet_lt hr ht)
  have hmoving : Measurable (fun w=>if q w<(carrier (Base (p w)) k).terminal (h w) ∧
      r w<(carrier (Base (p w)) k).terminal (h w) then
      fderiv ℝ (ActualMeanKernel.cappedAverage (Base (p w)) k (q w) (h w)) (m w)
        (weightedHeatRow Λ (S.observations w) (q w) (r w) (y w)) else (0:ℝ)) :=
    hv.ite hs (measurable_const (a:=(0:ℝ)))
  convert hmoving using 1
  funext w
  simp only [ActualMeanKernel.weightedPoint]
  split_ifs with hb
  · simp only [ActualMeanKernel.cappedAverage,min_eq_left hb.1.le]
    rfl
  · rfl

/-- True old-space average of the theta-dependent kernel is jointly
Borel with the outer parameter, current time/sample and output point.
The interpolation-dependent level itself is not taken as a fixed level. -/
theorem weightedSpatial_measurable (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p)
    (q r : W→ℝ) (hq : Measurable q) (hr : Measurable r)
    (m : W→History X k→WordRecursion.State (n+k))
    (hm : Measurable (fun z : W×History X k=>m z.1 z.2))
    (t : W→Fin k→ℝ) (ht : Measurable t) (x : W→X) (hx : Measurable x) :
    Measurable (fun z : W×HeatCircle=>ActualMeanKernel.weightedSpatial (Base (p z.1)) k Λ
      (q z.1) (r z.1) m (t z.1) z.1 z.2 (x z.1)) := by
  let Y:=(W×HeatCircle)×(Fin k→HeatCircle)
  let h : Y→History X k:=fun z=>separated k (x z.1.1,t z.1.1,z.2)
  have hh : Measurable h:=(separated_measurable k).comp
    ((hx.comp measurable_fst.fst).prodMk ((ht.comp measurable_fst.fst).prodMk measurable_snd))
  have hmean : Measurable (fun z : Y=>m z.1.1 (h z)):=hm.comp (measurable_fst.fst.prodMk hh)
  have hpoint:=weightedPoint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : Y=>p z.1.1) (hp.comp measurable_fst.fst) h hh
    (fun z : Y=>q z.1.1) (fun z : Y=>r z.1.1) (hq.comp measurable_fst.fst) (hr.comp measurable_fst.fst)
    (fun z : Y=>m z.1.1 (h z)) hmean (fun z : Y=>z.1.2) measurable_fst.snd
  have hi:=hpoint.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi)))
  have hc:=Complex.continuous_ofReal.measurable.comp hi.measurable
  convert hc using 1
  funext z
  unfold ActualMeanKernel.weightedSpatial
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  unfold ActualMeanKernel.weightedPoint
  rfl

end SHE.ControlledThetaWeightedFields
