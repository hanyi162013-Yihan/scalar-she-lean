module

public import SHE.HistoryRelativeSample
public import SHE.UniformFiberMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HistoryProductMeasure
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance historyAverageEnergy_period : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

/-- Genuine original-history/sample Fubini identifies the literal
history average with old-space, then old-time, then output-root
averaging. Absolute history integrability is required and used. -/
theorem history_average_relative_ae (R : ReferenceData) (k : ℕ)
    (F : Ω×History HeatCircle k→ℝ) (hF : Measurable F)
    (hi : Integrable F (μ.prod (historyMeasure R haarAddCircle k))) :
    ∀ᵐ ω ∂μ,(∫ h,F (ω,h) ∂historyMeasure R haarAddCircle k)=
      ∫ x:HeatCircle,∫ t:Fin k→ℝ,∫ w:Fin k→HeatCircle,
        F (ω,separated k (x,t,fun i=>w i+x))
          ∂Measure.pi (fun _=>haarAddCircle)
          ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)) ∂haarAddCircle := by
  let τ:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let η:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*π))
  have hmap:=relativeSeparated_preserving R k
  filter_upwards [hi.prod_right_ae] with ω hω
  let G:=fun z : (Fin k→ℝ)×(HeatCircle×(Fin k→HeatCircle))=>F (ω,relativeSeparated k z)
  have hG : Integrable G (τ.prod (haarAddCircle.prod η)):=hmap.integrable_comp_of_integrable hω
  have he : (∫ z,G z ∂τ.prod (haarAddCircle.prod η))=∫ h,F (ω,h) ∂historyMeasure R haarAddCircle k:=by
    rw [←hmap.map_eq,integral_map hmap.measurable.aemeasurable
      (by rw [hmap.map_eq];exact hω.aestronglyMeasurable)]
  have hAssoc:=(measurePreserving_prodAssoc τ (haarAddCircle (T:=2*π)) η).integrable_comp_of_integrable hG
  have hAvg : Integrable (fun z : (Fin k→ℝ)×HeatCircle=>∫ w,F (ω,separated k (z.2,z.1,fun i=>w i+z.2)) ∂η)
      (τ.prod haarAddCircle):=by
    convert! hAssoc.integral_prod_left using 1
  calc
    _=∫ z,G z ∂τ.prod (haarAddCircle.prod η):=he.symm
    _=∫ t,∫ x:HeatCircle,∫ w,F (ω,separated k (x,t,fun i=>w i+x)) ∂η ∂haarAddCircle ∂τ:=by
      rw [integral_prod _ hG]
      apply integral_congr_ae
      filter_upwards [hG.prod_right_ae] with t ht
      exact integral_prod _ ht
    _=∫ x:HeatCircle,∫ t,∫ w,F (ω,separated k (x,t,fun i=>w i+x)) ∂η ∂τ ∂haarAddCircle:=
      integral_integral_swap hAvg

/-- Original root averaging is a genuine probability contraction after
old space and old time have already been integrated. This transfers
actual native spatial RMS estimates to the ORIGINAL history average. -/
theorem history_average_energy [IsProbabilityMeasure μ] (R : ReferenceData) (k : ℕ)
    (F : Ω×History HeatCircle k→ℝ) (hF : Measurable F)
    (hi : Integrable F (μ.prod (historyMeasure R haarAddCircle k)))
    (hRMS : Integrable (fun z : Ω×HeatCircle=>
      |∫ t:Fin k→ℝ,∫ w:Fin k→HeatCircle,F (z.1,separated k (z.2,t,fun i=>w i+z.2))
        ∂Measure.pi (fun _=>haarAddCircle)
        ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))|^2) (μ.prod haarAddCircle)) :
    Integrable (fun ω=>|∫ h,F (ω,h) ∂historyMeasure R haarAddCircle k|^2) μ ∧
    (∫ ω,|∫ h,F (ω,h) ∂historyMeasure R haarAddCircle k|^2 ∂μ)≤
      ∫ z : Ω×HeatCircle,|∫ t:Fin k→ℝ,∫ w:Fin k→HeatCircle,F (z.1,separated k (z.2,t,fun i=>w i+z.2))
        ∂Measure.pi (fun _=>haarAddCircle)
        ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))|^2 ∂μ.prod haarAddCircle := by
  let τ:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let η:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*π))
  let B:=fun z : Ω×HeatCircle=>∫ t:Fin k→ℝ,∫ w:Fin k→HeatCircle,
    F (z.1,separated k (z.2,t,fun i=>w i+z.2)) ∂η ∂τ
  have hmRaw : Measurable (fun z : ((Ω×HeatCircle)×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      F (z.1.1.1,separated k (z.1.1.2,z.1.2,fun i=>z.2 i+z.1.1.2))) := by
    have hsites : Measurable (fun z : ((Ω×HeatCircle)×(Fin k→ℝ))×(Fin k→HeatCircle)=>
        fun i=>z.2 i+z.1.1.2):=Measurable.of_eval (fun i=>
      ((measurable_pi_apply i).comp measurable_snd).add measurable_fst.fst.snd)
    exact hF.comp (measurable_fst.fst.fst.prodMk ((separated_measurable k).comp
      (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk hsites))))
  have hmB : Measurable B:=hmRaw.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
  have hmem : MemLp B 2 (μ.prod haarAddCircle):=by
    apply (memLp_two_iff_integrable_sq hmB.aestronglyMeasurable).mpr
    simpa only [sq_abs] using hRMS
  have hh:=UniformFiberMoments.average_even_moment μ haarAddCircle B
    (hmem.integrable (by norm_num)) 1 hRMS
  have he : (fun ω=>|∫ h,F (ω,h) ∂historyMeasure R haarAddCircle k|^2)=ᵐ[μ]
      fun ω=>|∫ x:HeatCircle,B (ω,x) ∂haarAddCircle|^2:=by
    filter_upwards [history_average_relative_ae μ R k F hF hi] with ω hω
    exact congrArg (fun z:ℝ=>|z|^2) hω
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans_le (by simpa only [mul_one,one_mul] using hh.2)⟩

end SHE.HistoryProductMeasure
