module

public import SHE.ForestTranslation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.OrderedHeatForests
open Set Filter MeasureTheory AddCircle StoppedFourier
local instance forestJointTranslation_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- Root-dependent simultaneous translation of all old vertices is a
genuine product measure equivalence, not an exceptional-set diagonal. -/
def jointRelativeShift (k : ℕ) :
    (HeatCircle×(Fin k→HeatCircle)) ≃ᵐ (HeatCircle×(Fin k→HeatCircle)) where
  toFun p := (p.1,fun i=>p.2 i+p.1)
  invFun p := (p.1,fun i=>p.2 i-p.1)
  left_inv p := by ext i <;> simp only [add_sub_cancel_right]
  right_inv p := by ext i <;> simp only [sub_add_cancel]
  measurable_toFun := measurable_fst.prodMk (Measurable.of_eval (fun i=>
    ((measurable_pi_apply i).comp measurable_snd).add measurable_fst))
  measurable_invFun := measurable_fst.prodMk (Measurable.of_eval (fun i=>
    ((measurable_pi_apply i).comp measurable_snd).sub measurable_fst))

theorem jointRelativeShift_apply (k : ℕ) (p : HeatCircle×(Fin k→HeatCircle)) :
    jointRelativeShift k p=(p.1,fun i=>p.2 i+p.1) := rfl

theorem jointRelativeShift_preserving (k : ℕ) :
    MeasurePreserving (jointRelativeShift k)
      (haarAddCircle.prod (Measure.pi (fun _=>haarAddCircle)))
      (haarAddCircle.prod (Measure.pi (fun _=>haarAddCircle))) := by
  have hg0 : Measurable (fun p : HeatCircle×(Fin k→HeatCircle)=>fun i=>p.2 i+p.1) :=
    Measurable.of_eval (fun i=>
      ((measurable_pi_apply i).comp measurable_snd).add measurable_fst)
  have hg : Measurable (Function.uncurry (fun x=>relativeShift k x)) := by
    convert! hg0 using 1
  exact (MeasurePreserving.id haarAddCircle).skew_product
    hg
    (ae_of_all _ (fun x=>(relativeShift_preserving k x).map_eq))

/-- Every common old-space/root AE event transfers to relative
coordinates before choosing the root location. -/
theorem ae_relative_sections (k : ℕ) (P : HeatCircle×(Fin k→HeatCircle)→Prop)
    (hP : ∀ᵐ p ∂haarAddCircle.prod (Measure.pi (fun _=>haarAddCircle)),P p) :
    ∀ᵐ x ∂haarAddCircle,∀ᵐ w ∂Measure.pi (fun _ : Fin k=>haarAddCircle),
      P (x,fun i=>w i+x) := by
  exact Measure.ae_ae_of_ae_prod ((jointRelativeShift_preserving k).quasiMeasurePreserving.ae hP)

end SHE.OrderedHeatForests
