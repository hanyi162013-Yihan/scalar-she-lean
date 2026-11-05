module

public import SHE.InitialTerminalFields
public import SHE.InitialTerminalFibre
public import SHE.RootHistoryFubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.InitialSpatialFields
open Classical Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry SmoothCylinders UniformSmooth HistoryProductMeasure
local instance initialSpatialFields_period:Fact (0<2*Real.pi):=⟨by positivity⟩
variable (R:ReferenceData)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
variable {Ω:Type} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable (Λ:ℝ) (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)

/-- Only original old histories are averaged; the native output remains. -/
def value (k:ℕ) (T:Icc R.base R.horizon) (y:Ω×HeatCircle):ℝ:=
  ∫t:Fin k→ℝ,∫w:Fin k→HeatCircle,
    InitialTerminalFields.point R F hF hFm Λ U V XU XV k T (separated k (y.2,t,fun j=>w j+y.2)) y.1
    ∂Measure.pi (fun _=>AddCircle.haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))

variable (hU:Measurable U) (hV:Measurable V) (hXU:Measurable XU) (hXV:Measurable XV)
include hU hV hXU hXV in
theorem value_measurable (k:ℕ):Measurable (fun z:Icc R.base R.horizon×(Ω×HeatCircle)=>
    value R F hF hFm Λ U V XU XV k z.1 z.2):=by
  have hs:Measurable (fun z:((Icc R.base R.horizon×(Ω×HeatCircle))×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      separated k (z.1.1.2.2,z.1.2,fun j=>z.2 j+z.1.1.2.2)):=by
    apply (separated_measurable k).comp
    exact measurable_fst.fst.snd.snd.prodMk (measurable_fst.snd.prodMk
      (Measurable.of_eval (fun j=>(measurable_pi_apply j).comp measurable_snd |>.add measurable_fst.fst.snd.snd)))
  have hm:Measurable (fun z:((Icc R.base R.horizon×(Ω×HeatCircle))×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      InitialTerminalFields.point R F hF hFm Λ U V XU XV k z.1.1.1
        (separated k (z.1.1.2.2,z.1.2,fun j=>z.2 j+z.1.1.2.2)) z.1.1.2.1):=
    (InitialTerminalFields.point_measurable R F hF hFm Λ U V XU XV hU hV hXU hXV k).comp
      ((measurable_fst.fst.fst.prodMk hs).prodMk measurable_fst.fst.snd.fst)
  exact (hm.stronglyMeasurable.integral_prod_right'.measurable.stronglyMeasurable.integral_prod_right').measurable

/-- The original restricted old-time product changes horizon exactly
by restriction to the original node box. -/
theorem time_measure {a T h:ℝ} (hT:T≤h) (k:ℕ):
    Measure.pi (fun _:Fin k=>volume.restrict (Ioc a T))=
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc a h))).restrict (Set.univ.pi (fun _=>Iic T)):=by
  rw [Measure.restrict_pi_pi (μ:=fun _:Fin k=>volume.restrict (Ioc a h)) (fun _=>Iic T)]
  congr 1
  funext j
  rw [Measure.restrict_restrict measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_inter_iff,mem_Iic,mem_Ioc]
  constructor
  · rintro ⟨ha,ht⟩
    exact ⟨ht,ha,ht.trans hT⟩
  · rintro ⟨ht,ha,hh⟩
    exact ⟨ha,ht⟩

theorem separated_box (T:ℝ) (k:ℕ) (x:HeatCircle) (t:Fin k→ℝ) (w:Fin k→HeatCircle):
    separated k (x,t,w)∈HistoryHorizonIntegration.box T k ↔ ∀j,t j≤T:=by
  induction k with
  | zero=>exact ⟨fun _ j=>Fin.elim0 j,fun _=>mem_univ _⟩
  | succ k ih=>
    change (separated k (x,(fun j=>t j.succ),(fun j=>w j.succ))∈HistoryHorizonIntegration.box T k ∧
      t 0≤T ∧ True)↔∀j:Fin (k+1),t j≤T
    rw [ih]
    constructor
    · rintro ⟨ht,h0,htrue⟩ j
      exact Fin.cases h0 ht j
    · intro ht
      exact ⟨fun j=>ht j.succ,ht 0,trivial⟩

/-- Pointwise horizon change for a true output-retained average.
No integrability or spatial averaging premise is required. -/
theorem root_average_horizon {Q:ReferenceData} (hb:Q.base=R.base) (hT:Q.horizon≤R.horizon)
    (k:ℕ) (f:Ω×History HeatCircle k→ℝ)
    (hs:∀ω p,p∉HistoryHorizonIntegration.box Q.horizon k→f (ω,p)=0) (y:Ω×HeatCircle):
    rootAverage Q k f y=rootAverage R k f y:=by
  unfold rootAverage
  rw [hb,time_measure hT k,←integral_indicator
    (MeasurableSet.univ_pi (fun _=>measurableSet_Iic))]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht:t∈Set.univ.pi (fun _:Fin k=>Iic Q.horizon)
  · simp only [indicator_of_mem ht]
  · simp only [Set.indicator_apply,if_neg ht]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards with w
    apply hs y.1
    rw [separated_box]
    simpa only [mem_pi,mem_univ,true_implies,not_forall,mem_Iic] using ht

end SHE.InitialSpatialFields
