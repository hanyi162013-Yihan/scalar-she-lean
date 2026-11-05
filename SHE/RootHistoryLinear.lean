module

public import SHE.RootHistoryFubini

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance rootHistoryLinear_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

theorem root_average_product_ae (R : ReferenceData) (k : ℕ)
    (τ : Measure Θ) [SFinite τ] (μ : Measure Ω) [SFinite μ]
    (F : Θ×(Ω×History HeatCircle k)→ℝ)
    (hi : Integrable F (τ.prod (μ.prod (historyMeasure R haarAddCircle k)))) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod haarAddCircle,
      let B:=(Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
        (Measure.pi (fun _ : Fin k=>haarAddCircle))
      let G:=fun a : Θ×((Fin k→ℝ)×(Fin k→HeatCircle))=>
        F (a.1,(z.1,separated k (z.2,a.2.1,fun i=>a.2.2 i+z.2)))
      Integrable G (τ.prod B) ∧
      Integrable (fun θ=>rootAverage R k (fun a=>F (θ,a)) z) τ ∧
      (∫ θ,rootAverage R k (fun a=>F (θ,a)) z ∂τ)=∫ a,G a ∂τ.prod B := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let G : (Ω×HeatCircle)×(Θ×((Fin k→ℝ)×(Fin k→HeatCircle)))→ℝ:=fun z=>
    F (z.2.1,(z.1.1,separated k (z.1.2,z.2.2.1,fun i=>z.2.2.2 i+z.1.2)))
  have hp:=rootTheta_preserving R τ μ k
  have hG : Integrable G ((μ.prod haarAddCircle).prod (τ.prod (T.prod W))):=
    (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  filter_upwards [hG.prod_right_ae] with z hz
  have hleft : (fun θ=>rootAverage R k (fun a=>F (θ,a)) z)=ᵐ[τ]
      fun θ=>∫ a,G (z,(θ,a)) ∂T.prod W := by
    filter_upwards [hz.prod_right_ae] with θ hθ
    exact (integral_prod _ hθ).symm
  exact ⟨hz,hz.integral_prod_left.congr hleft.symm,
    (integral_congr_ae hleft).trans (integral_prod _ hz).symm⟩

/-- Genuine finite-linearity of the root-retained theta/history
average, proved from absolute component masses before cancellation. -/
theorem root_theta_sum_three (R : ReferenceData) (k : ℕ)
    (τ : Measure Θ) [SFinite τ] (μ : Measure Ω) [SFinite μ]
    (C M B : Θ×(Ω×History HeatCircle k)→ℝ)
    (hC : Integrable C (τ.prod (μ.prod (historyMeasure R haarAddCircle k))))
    (hM : Integrable M (τ.prod (μ.prod (historyMeasure R haarAddCircle k))))
    (hB : Integrable B (τ.prod (μ.prod (historyMeasure R haarAddCircle k)))) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod haarAddCircle,
      (∫ θ,rootAverage R k (fun a=>C (θ,a)+M (θ,a)+B (θ,a)) z ∂τ)=
      (∫ θ,rootAverage R k (fun a=>C (θ,a)) z ∂τ)+
      (∫ θ,rootAverage R k (fun a=>M (θ,a)) z ∂τ)+
      (∫ θ,rootAverage R k (fun a=>B (θ,a)) z ∂τ) := by
  have hc:=root_average_product_ae R k τ μ C hC
  have hm:=root_average_product_ae R k τ μ M hM
  have hb:=root_average_product_ae R k τ μ B hB
  have hs:=root_average_product_ae R k τ μ (C+M+B) ((hC.add hM).add hB)
  filter_upwards [hc,hm,hb,hs] with z hc hm hb hs
  calc
    _=_:=hs.2.2
    _=(∫ a,C (a.1,(z.1,separated k (z.2,a.2.1,fun i=>a.2.2 i+z.2)))
        ∂τ.prod ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
          (Measure.pi (fun _ : Fin k=>haarAddCircle))))+
      (∫ a,M (a.1,(z.1,separated k (z.2,a.2.1,fun i=>a.2.2 i+z.2)))
        ∂τ.prod ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
          (Measure.pi (fun _ : Fin k=>haarAddCircle))))+
      (∫ a,B (a.1,(z.1,separated k (z.2,a.2.1,fun i=>a.2.2 i+z.2)))
        ∂τ.prod ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
          (Measure.pi (fun _ : Fin k=>haarAddCircle)))) := by
      exact (integral_add (hc.1.add hm.1) hb.1).trans
        (congrArg (fun r : ℝ=>r+∫ a,B (a.1,(z.1,separated k (z.2,a.2.1,fun i=>a.2.2 i+z.2)))
          ∂τ.prod ((Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))).prod
            (Measure.pi (fun _ : Fin k=>haarAddCircle)))) (integral_add hc.1 hm.1))
    _=_:=by rw [←hc.2.2,←hm.2.2,←hb.2.2]

end SHE.HistoryProductMeasure
