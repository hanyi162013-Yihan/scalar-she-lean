module

public import SHEStochastic.HolderWeightedEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NormalizedHolderEnergy
open MeasureTheory
open scoped NNReal ENNReal

/-- On a probability spatial domain, the constant part of Holder growth
has the same interpolated kernel bound as its variable part. This
removes the unit-time restriction from the heat-increment estimate. -/
theorem bound {X E V : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup V]
    {ν : Measure X} [IsProbabilityMeasure ν] {G : E → V} {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ1 : β≤1) (u : Lp E 2 ν)
    (h : X → ℝ≥0∞) (hh : AEMeasurable h ν) (L Q : ℝ≥0∞)
    (hcap : ∀ᵐ x ∂ν, h x≤L) (henergy : (∫⁻ x, h x ∂ν)≤Q) :
    (∫⁻ x, h x*ENNReal.ofReal (‖G (u x)‖^2) ∂ν)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2)*(L^(β:ℝ)*Q^(1-(β:ℝ)))*
        (1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by
  let M := ∫⁻ x, h x ∂ν
  have hβ : (β:ℝ)≤1 := by exact_mod_cast hβ1
  have hb := WeightedSublinearEnergy.energy_interpolation ν h (fun _ ↦ 1) hh aemeasurable_const
    L hcap β.property hβ
  have hbase : M≤L^(β:ℝ)*M^(1-(β:ℝ)) := by
    simp only [ENNReal.one_rpow, mul_one, lintegral_one, measure_univ] at hb
    convert! hb using 1
  have hw := HolderWeightedEnergy.bound hG hβ1 u h hh L M hcap le_rfl
  calc
    _ ≤ ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2)*(M+L^(β:ℝ)*(M^(1-(β:ℝ))*ENNReal.ofReal (‖u‖^2)^(β:ℝ))) := hw
    _ ≤ ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2)*
        (L^(β:ℝ)*M^(1-(β:ℝ))+L^(β:ℝ)*(M^(1-(β:ℝ))*ENNReal.ofReal (‖u‖^2)^(β:ℝ))) := by gcongr
    _ = ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2)*(L^(β:ℝ)*M^(1-(β:ℝ)))*(1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by ring
    _ ≤ _ := by gcongr

end SHEStochastic.NormalizedHolderEnergy
