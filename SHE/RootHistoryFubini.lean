module

public import SHE.RootHistoryMeasure

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance rootHistoryFubini_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- Average only the original old times/locations; retain the sample
and true output root as coordinates. -/
def rootAverage (R : ReferenceData) (k : ℕ) (F : Ω×History HeatCircle k→ℝ)
    (z : Ω×HeatCircle) : ℝ :=
  ∫ t : Fin k→ℝ,∫ w : Fin k→HeatCircle,
    F (z.1,separated k (z.2,t,fun i=>w i+z.2))
    ∂Measure.pi (fun _=>haarAddCircle)
    ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))

/-- Honest theta/history Fubini retaining the output coordinate.
The input is absolute product integrability, before any cancellation. -/
theorem root_average_swap (R : ReferenceData) (k : ℕ)
    (τ : Measure Θ) [SFinite τ] (μ : Measure Ω) [SFinite μ]
    (F : Θ×(Ω×History HeatCircle k)→ℝ) (hF : Measurable F)
    (hi : Integrable F (τ.prod (μ.prod (historyMeasure R haarAddCircle k)))) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod haarAddCircle,
      Integrable (fun θ=>rootAverage R k (fun a=>F (θ,a)) z) τ ∧
      (∫ θ,rootAverage R k (fun a=>F (θ,a)) z ∂τ)=
        rootAverage R k (fun a=>∫ θ,F (θ,a) ∂τ) z := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let G : (Ω×HeatCircle)×(Θ×((Fin k→ℝ)×(Fin k→HeatCircle)))→ℝ:=fun z=>
    F (z.2.1,(z.1.1,separated k (z.1.2,z.2.2.1,fun i=>z.2.2.2 i+z.1.2)))
  have hp:=rootTheta_preserving R τ μ k
  have hG : Integrable G ((μ.prod haarAddCircle).prod (τ.prod (T.prod W))):=
    (hp.integrable_comp hF.aestronglyMeasurable).mpr hi
  filter_upwards [hG.prod_right_ae] with z hz
  have hleft : (fun θ=>rootAverage R k (fun a=>F (θ,a)) z)=ᵐ[τ]
      fun θ=>∫ a,G (z,(θ,a)) ∂T.prod W := by
    filter_upwards [hz.prod_right_ae] with θ hθ
    exact (integral_prod _ hθ).symm
  refine ⟨hz.integral_prod_left.congr hleft.symm,?_⟩
  rw [integral_congr_ae hleft]
  calc
    _=∫ a,∫ θ,G (z,(θ,a)) ∂τ ∂T.prod W:=integral_integral_swap hz
    _=rootAverage R k (fun a=>∫ θ,F (θ,a) ∂τ) z:=
      integral_prod _ hz.swap.integral_prod_left

/-- A common original-history equality can be substituted into the
root-retained average before any spatial or sample square. -/
theorem root_average_congr_ae (R : ReferenceData) (k : ℕ)
    (μ : Measure Ω) [SFinite μ] (F G : Ω×History HeatCircle k→ℝ)
    (he : F=ᵐ[μ.prod (historyMeasure R haarAddCircle k)] G) :
    rootAverage R k F=ᵐ[μ.prod haarAddCircle] rootAverage R k G := by
  have hh:=(rootSample_preserving R μ k).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hh] with z hz
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hz] with t ht
  exact integral_congr_ae ht

theorem root_average_sub_ae (R : ReferenceData) (k : ℕ)
    (μ : Measure Ω) [SFinite μ] (F G : Ω×History HeatCircle k→ℝ)
    (hF : Integrable F (μ.prod (historyMeasure R haarAddCircle k)))
    (hG : Integrable G (μ.prod (historyMeasure R haarAddCircle k))) :
    rootAverage R k (F-G)=ᵐ[μ.prod haarAddCircle]
      (fun z=>rootAverage R k F z-rootAverage R k G z) := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let f : (Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))→ℝ:=fun z=>
    F (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2))
  let g : (Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))→ℝ:=fun z=>
    G (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2))
  have hp:=rootSample_preserving R μ k
  have hf : Integrable f ((μ.prod haarAddCircle).prod (T.prod W)):=
    (hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hg : Integrable g ((μ.prod haarAddCircle).prod (T.prod W)):=
    (hp.integrable_comp hG.aestronglyMeasurable).mpr hG
  filter_upwards [hf.prod_right_ae,hg.prod_right_ae] with z hzF hzG
  change (∫ t,∫ w,f (z,(t,w))-g (z,(t,w)) ∂W ∂T)=
    (∫ t,∫ w,f (z,(t,w)) ∂W ∂T)-(∫ t,∫ w,g (z,(t,w)) ∂W ∂T)
  calc
    _=(∫ a,f (z,a)-g (z,a) ∂T.prod W):=(integral_prod _ (hzF.sub hzG)).symm
    _=(∫ a,f (z,a) ∂T.prod W)-(∫ a,g (z,a) ∂T.prod W):=integral_sub hzF hzG
    _=_:=congrArg₂ HSub.hSub (integral_prod _ hzF) (integral_prod _ hzG)

end SHE.HistoryProductMeasure
