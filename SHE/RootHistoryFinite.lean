module

public import SHE.RootHistoryFubini

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SHE.HistoryProductMeasure
open Set MeasureTheory AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
local instance rootHistoryFinite_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]

theorem root_average_integrable (R : ReferenceData) (k : ℕ)
    (μ : Measure Ω) [SFinite μ] (F : Ω×History HeatCircle k→ℝ)
    (hi : Integrable F (μ.prod (historyMeasure R haarAddCircle k))) :
    Integrable (rootAverage R k F) (μ.prod haarAddCircle) := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let f : (Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))→ℝ:=fun z=>
    F (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2))
  have hf : Integrable f ((μ.prod haarAddCircle).prod (T.prod W)):=
    ((rootSample_preserving R μ k).integrable_comp hi.aestronglyMeasurable).mpr hi
  apply hf.integral_prod_left.congr
  filter_upwards [hf.prod_right_ae] with z hz
  exact integral_prod _ hz

/-- Finite root sums pass through the genuine original old-time/space
average only after absolute component integrability has been proved. -/
theorem root_average_finsetSum (R : ReferenceData) (k : ℕ)
    (μ : Measure Ω) [SFinite μ] (F : ℕ→Ω×History HeatCircle k→ℝ)
    (hi : ∀ j,Integrable (F j) (μ.prod (historyMeasure R haarAddCircle k))) (s : Finset ℕ) :
    rootAverage R k (fun a=>∑ j∈s,F j a)=ᵐ[μ.prod haarAddCircle]
      fun z=>∑ j∈s,rootAverage R k (F j) z := by
  let T:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let f : ℕ→(Ω×HeatCircle)×((Fin k→ℝ)×(Fin k→HeatCircle))→ℝ:=fun j z=>
    F j (z.1.1,separated k (z.1.2,z.2.1,fun i=>z.2.2 i+z.1.2))
  have hj (j : ℕ) : Integrable (f j) ((μ.prod haarAddCircle).prod (T.prod W)):=
    ((rootSample_preserving R μ k).integrable_comp (hi j).aestronglyMeasurable).mpr (hi j)
  filter_upwards [ae_all_iff.2 (fun j=>(hj j).prod_right_ae)] with z hz
  change (∫ t,∫ w,∑ j∈s,f j (z,(t,w)) ∂W ∂T)=
    ∑ j∈s,∫ t,∫ w,f j (z,(t,w)) ∂W ∂T
  calc
    _=∫ a,∑ j∈s,f j (z,a) ∂T.prod W:=
      (integral_prod _ (integrable_finset_sum s (fun j _=>hz j))).symm
    _=∑ j∈s,∫ a,f j (z,a) ∂T.prod W:=integral_finsetSum s (fun j _=>hz j)
    _=_:=Finset.sum_congr rfl (fun j _=>integral_prod _ (hz j))

end SHE.HistoryProductMeasure
