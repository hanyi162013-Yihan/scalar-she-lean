module

public import SHE.HeatForestProduct
public import SHE.StoppedScoreTranslation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory AddCircle StoppedFourier NativeHeatAction
local instance forestTranslation_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

theorem values_translate {m : ℕ} (a : Fin m→HeatCircle) (k : ℕ)
    (w : Fin k→HeatCircle) (x : HeatCircle) :
    values (fun i=>a i+x) k (fun i=>w i+x)=fun i=>values a k w i+x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · exact congrFun (ih (fun j=>w j.succ)) j

theorem density_translate {m k : ℕ} (T : Forest m k)
    (z : Fin (m+k)→HeatCircle) (x : HeatCircle) :
    density T (fun i=>z i+x)=density T z := by
  induction T with
  | roots => rfl
  | branch T parent gap hg ih =>
    change density T (fun i=>z i.succ+x)*edge gap hg (z parent.succ+x) (z 0+x)=
      density T (fun i=>z i.succ)*edge gap hg (z parent.succ) (z 0)
    rw [ih]
    simp only [edge,NativeHeatSpan.kernel_eq_physical,StoppedScoreLeverage.heatPhysical_translate]

def relativeShift (k : ℕ) (x : HeatCircle) :
    (Fin k→HeatCircle) ≃ᵐ (Fin k→HeatCircle) :=
  MeasurableEquiv.piCongrRight (fun _=>MeasurableEquiv.addRight x)

theorem relativeShift_apply (k : ℕ) (x : HeatCircle) (w : Fin k→HeatCircle) :
    relativeShift k x w=fun i=>w i+x := rfl

theorem relativeShift_preserving (k : ℕ) (x : HeatCircle) :
    MeasurePreserving (relativeShift k x)
      (Measure.pi (fun _=>haarAddCircle)) (Measure.pi (fun _=>haarAddCircle)) := by
  exact measurePreserving_pi _ _ (fun _=>measurePreserving_add_right haarAddCircle x)

/-- The full old-space integral is exactly the translated relative
forest integral. Every old vertex moves with the root; none is fixed or
identified during the change of variables. -/
theorem integral_relative_coordinates {m k : ℕ} (T : Forest m k)
    (a : Fin m→HeatCircle) (F : (Fin (m+k)→HeatCircle)→ℝ) (x : HeatCircle) :
    (∫ w : Fin k→HeatCircle,density T (values (fun i=>a i+x) k w)*F (values (fun i=>a i+x) k w)
      ∂Measure.pi (fun _=>haarAddCircle))=
    ∫ w : Fin k→HeatCircle,density T (values a k w)*F (fun i=>values a k w i+x)
      ∂Measure.pi (fun _=>haarAddCircle) := by
  rw [←(relativeShift_preserving k x).integral_comp']
  apply integral_congr_ae
  exact ae_of_all _ (fun w=>by
    dsimp only
    rw [relativeShift_apply,values_translate,density_translate])

end SHE.OrderedHeatForests
