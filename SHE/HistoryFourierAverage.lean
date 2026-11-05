module

public import SHE.NativeFourierSections
public import SHE.RootHistoryFubini
public import SHE.ForestTranslation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories OrderedHeatForests
local instance historyFourierAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]

def oldSpaceAverage (k : ℕ) (F : Ω×History HeatCircle k→ℝ)
    (z : (Fin k→ℝ)×(Ω×HeatCircle)) : ℝ :=
  ∫ w : Fin k→HeatCircle,F (z.2.1,separated k (z.2.2,z.1,fun i=>w i+z.2.2))
    ∂Measure.pi (fun _=>haarAddCircle)

theorem oldSpaceAverage_absolute (k : ℕ) (F : Ω×History HeatCircle k→ℝ)
    (t : Fin k→ℝ) (ω : Ω) (x : HeatCircle) :
    oldSpaceAverage k F (t,(ω,x))=
      ∫ w : Fin k→HeatCircle,F (ω,separated k (x,t,w)) ∂Measure.pi (fun _=>haarAddCircle) := by
  exact (relativeShift_preserving k x).integral_comp' (fun w=>F (ω,separated k (x,t,w)))

/-- Absolute original-history L¹ mass gives genuine parameter/sample/
output L¹ mass after averaging the old spaces. -/
theorem oldSpaceAverage_integrable (R : ReferenceData) (μ : Measure Ω) [SFinite μ]
    (k : ℕ) (F : Ω×History HeatCircle k→ℝ)
    (hi : Integrable F (μ.prod (historyMeasure R haarAddCircle k))) :
    Integrable (oldSpaceAverage k F)
      ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
        (μ.prod haarAddCircle)) := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  have hp := (relativeSample_preserving R μ k).comp
    (measurePreserving_prodAssoc T (μ.prod (haarAddCircle : Measure HeatCircle)) W)
  have hf : Integrable (fun z : ((Fin k→ℝ)×(Ω×HeatCircle))×(Fin k→HeatCircle)=>
      F (z.1.2.1,separated k (z.1.2.2,z.1.1,fun i=>z.2 i+z.1.2.2)))
      ((T.prod (μ.prod haarAddCircle)).prod W) := by
    convert! (hp.integrable_comp hi.aestronglyMeasurable).mpr hi using 1
  exact hf.integral_prod_left

theorem root_average_fourier (R : ReferenceData) (μ : Measure Ω) [SFinite μ]
    (k : ℕ) (F : Ω×History HeatCircle k→ℝ)
    (V : (Fin k→ℝ)×Ω→CircleL2)
    (hF : Integrable F (μ.prod (historyMeasure R haarAddCircle k)))
    (hV : Integrable V ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod μ))
    (w : ℤ→ℂ)
    (hc : ∀ t ω n,fourierCoeff (V (t,ω)) n=w n*fourierCoeff
      (fun x=>Complex.ofReal (∫ y : Fin k→HeatCircle,F (ω,separated k (x,t,y))
        ∂Measure.pi (fun _=>haarAddCircle))) n) :
    ∀ᵐ ω ∂μ,∀ n,
      fourierCoeff (∫ t,V (t,ω) ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)) : CircleL2) n=
      w n*fourierCoeff (fun x=>Complex.ofReal (rootAverage R k F (ω,x))) n := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let g : (Fin k→ℝ)×(Ω×HeatCircle)→ℂ:=fun z=>Complex.ofReal (oldSpaceAverage k F z)
  have hg : Integrable g (T.prod (μ.prod haarAddCircle)):=
    Complex.ofRealCLM.integrable_comp (oldSpaceAverage_integrable R μ k F hF)
  have hcoeff : ∀ᵐ z ∂T.prod μ,∀ n,fourierCoeff (V z) n=w n*fourierCoeff (fun x=>g (z.1,(z.2,x))) n := by
    filter_upwards with z n
    simpa only [g,oldSpaceAverage_absolute] using hc z.1 z.2 n
  have havg:=NativeFourierAverage.parameter_average_ae T μ V g hV hg w hcoeff
  have hgi:=oldSpaceAverage_integrable R μ k F hF
  have hp := (measurePreserving_prodAssoc T μ (haarAddCircle : Measure HeatCircle)).comp
    (((Measure.measurePreserving_swap (μ:=μ) (ν:=T)).prod
      (MeasurePreserving.id (haarAddCircle : Measure HeatCircle))).comp
      (measurePreserving_prodAssoc μ T (haarAddCircle : Measure HeatCircle)).symm)
  have hgs : Integrable (fun z : Ω×((Fin k→ℝ)×HeatCircle)=>oldSpaceAverage k F (z.2.1,(z.1,z.2.2)))
      (μ.prod (T.prod haarAddCircle)) := by
    convert! (hp.integrable_comp hgi.aestronglyMeasurable).mpr hgi using 1
  filter_upwards [havg,hgs.prod_right_ae] with ω hω hiω n
  rw [hω n]
  congr 1
  apply congrFun (fourierCoeff_congr_ae ?_) n
  filter_upwards [hiω.swap.prod_right_ae] with x hx
  exact Complex.ofRealCLM.integral_comp_comm hx

variable {Θ : Type*} [MeasurableSpace Θ]

theorem thetaRootAverage_measurable (R : ReferenceData) (k : ℕ)
    (F : Θ×(Ω×History HeatCircle k)→ℝ) (hF : Measurable F) :
    Measurable (fun z : Θ×(Ω×HeatCircle)=>rootAverage R k (fun a=>F (z.1,a)) z.2) := by
  have hm : Measurable (fun z : ((Θ×(Ω×HeatCircle))×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      F (z.1.1.1,(z.1.1.2.1,separated k (z.1.1.2.2,z.1.2,fun i=>z.2 i+z.1.1.2.2)))) := by
    apply hF.comp
    refine measurable_fst.fst.fst.prodMk (measurable_fst.fst.snd.fst.prodMk ?_)
    apply (separated_measurable k).comp
    exact measurable_fst.fst.snd.snd.prodMk (measurable_fst.snd.prodMk
      (Measurable.of_eval (fun i=>((measurable_pi_apply i).comp measurable_snd).add
        measurable_fst.fst.snd.snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

/-- Absolute theta/sample/original-history mass yields absolute mass of
the actual theta/root-retained history average, before cancellation. -/
theorem thetaRootAverage_integrable (R : ReferenceData) (k : ℕ)
    (τ : Measure Θ) [SFinite τ] (μ : Measure Ω) [SFinite μ]
    (F : Θ×(Ω×History HeatCircle k)→ℝ)
    (hi : Integrable F (τ.prod (μ.prod (historyMeasure R haarAddCircle k)))) :
    Integrable (fun z : Θ×(Ω×HeatCircle)=>rootAverage R k (fun a=>F (z.1,a)) z.2)
      (τ.prod (μ.prod haarAddCircle)) := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  have hp:=((MeasurePreserving.id τ).prod (rootSample_preserving R μ k)).comp
    (measurePreserving_prodAssoc τ (μ.prod (haarAddCircle : Measure HeatCircle)) (T.prod W))
  let G : (Θ×(Ω×HeatCircle))×((Fin k→ℝ)×(Fin k→HeatCircle))→ℝ:=fun z=>
    F (z.1.1,(z.1.2.1,separated k (z.1.2.2,z.2.1,fun i=>z.2.2 i+z.1.2.2)))
  have hG : Integrable G ((τ.prod (μ.prod haarAddCircle)).prod (T.prod W)) := by
    convert! (hp.integrable_comp hi.aestronglyMeasurable).mpr hi using 1
  apply hG.integral_prod_left.congr
  filter_upwards [hG.prod_right_ae] with z hz
  exact integral_prod _ hz

end SHE.HistoryProductMeasure
