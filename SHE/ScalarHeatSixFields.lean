module

public import SHE.ScalarHeatPairedGamma
public import SHE.NativePairedColumnFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.ScalarHeatSixFields
open Set MeasureTheory StoppedFourier SmoothCylinders ScalarHeatSingleMultiplier
local instance scalarHeatSixFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {P : Type*} [MeasurableSpace P]

def fields (a : ℝ→ℝ) (j : ℕ) (σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ) : Fin 6→P×HeatCircle→ℂ:=
  ![field a j σ0 z0,field a j σ0 z1,field a j σ1 z1,
    field a j σ0 m0,field a j σ0 m1,field a j σ1 m1]

theorem measurable {a : ℝ→ℝ} (ha : BoundedSmooth a) (j : ℕ)
    {σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ}
    (hσ0 : Measurable σ0) (hσ1 : Measurable σ1) (hz0 : Measurable z0) (hz1 : Measurable z1)
    (hm0 : Measurable m0) (hm1 : Measurable m1) (i : Fin 6) :
    Measurable (fields a j σ0 σ1 z0 z1 m0 m1 i) := by
  fin_cases i <;> simp only [fields,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact field_measurable ha j hσ0 hz0
  · exact field_measurable ha j hσ0 hz1
  · exact field_measurable ha j hσ1 hz1
  · exact field_measurable ha j hσ0 hm0
  · exact field_measurable ha j hσ0 hm1
  · exact field_measurable ha j hσ1 hm1

theorem bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    (σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ) (i : Fin 6) (p : P) (x : HeatCircle) :
    ‖fields a j σ0 σ1 z0 z1 m0 m1 i (p,x)‖≤cap H β j := by
  fin_cases i <;> simp only [fields,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals exact field_bound ha hH hβ hβ1 hh j _ _ p x

theorem nativeRow (a : ℝ→ℝ) (j : ℕ) (σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ) (p : P) (i : Fin 6) :
    NativeRandomRows.nativeRow (fields a j σ0 σ1 z0 z1 m0 m1 i) p=
      ScalarHeatPairedMultipliers.six a j σ0 σ1 z0 z1 m0 m1 p i := by
  fin_cases i <;> rfl

theorem multiplier_cap_irrel (b : CircleL2) (B C : ℝ)
    (hb : ∀ᵐ x∂AddCircle.haarAddCircle,‖b x‖≤B)
    (hc : ∀ᵐ x∂AddCircle.haarAddCircle,‖b x‖≤C) (v : CircleL2) :
    NativeMultiplierTrace.multiplier b B hb v=NativeMultiplierTrace.multiplier b C hc v := by
  apply Lp.ext
  filter_upwards [NativeMultiplierTrace.multiplier_ae b B hb v,
    NativeMultiplierTrace.multiplier_ae b C hc v] with x hx hy
  exact hx.trans hy.symm

end SHE.ScalarHeatSixFields
