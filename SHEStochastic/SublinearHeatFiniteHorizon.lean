module

public import SHEStochastic.SublinearHeatIntegratedEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.SublinearHeatFiniteHorizon
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle
open SublinearHeatRows SublinearHeatIntegratedEnergy
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The unit-time heat cap extends to any fixed finite horizon.
Only its constant changes; the integrable singular exponent is retained. -/
def constant (L : ℝ) : ℝ := L ^ (1/2 : ℝ)+heatConstant*2 ^ (1/2 : ℝ)

theorem constant_nonneg {L : ℝ} (hL : 0≤L) : 0≤constant L := by
  have hC := heatConstant_pos
  unfold constant
  positivity

theorem cap_bound {t L : ℝ} (ht : 0<t) (htL : t≤L) :
    cap t≤constant L*t ^ (-(1/2 : ℝ)) := by
  have hp := Real.rpow_le_rpow ht.le htL (by norm_num : (0:ℝ)≤1/2)
  have he : t^(1/2 : ℝ)*t^(-(1/2 : ℝ))=1 := by
    rw [← Real.rpow_add ht]
    norm_num
  have hone : 1≤L^(1/2 : ℝ)*t^(-(1/2 : ℝ)) := by
    calc
      _ = t^(1/2 : ℝ)*t^(-(1/2 : ℝ)) := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hdiv : (t/2)^(-(1/2 : ℝ))=t^(-(1/2 : ℝ))*2^(1/2 : ℝ) := by
    rw [Real.div_rpow ht.le (by norm_num : (0:ℝ)≤2), Real.rpow_neg (by norm_num : (0:ℝ)≤2), div_inv_eq_mul]
  unfold cap constant
  rw [hdiv]
  nlinarith

theorem cap_power_bound {t L β : ℝ} (ht : 0<t) (htL : t≤L) (hβ : 0≤β) :
    cap t^(1+β)≤constant L^(1+β)*t^(-(1+β)/2) := by
  have hc := constant_nonneg (ht.le.trans htL)
  have hh := Real.rpow_le_rpow (SublinearHeatRows.cap_nonneg ht.le)
    (cap_bound ht htL) (by linarith : 0≤1+β)
  rw [Real.mul_rpow hc (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le] at hh
  convert hh using 1
  congr 2
  ring

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

theorem coefficient_energy {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β≤1)
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) {t L : ℝ}
    (ht : 0<t) (htL : t≤L) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖^2*‖G (u x)‖^2) ∂haarAddCircle)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*constant L^(1+(β:ℝ))*t^(-(1+(β:ℝ))/2))*
        (1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by
  simpa only [mul_assoc] using SublinearHeatCoefficientEnergy.bound_of_cap_power hG hβ1 u ht a
    (constant L^(1+(β:ℝ))*t^(-(1+(β:ℝ))/2)) (cap_power_bound ht htL β.property)

/-- The localized unbounded heat row has finite bracket on every finite
horizon, with the same subcritical Holder exponent β<1. -/
theorem row_bound_until {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β<1)
    (T H : ℝ≥0) (hTH : T≤H) (L : ℝ) (hTL : (T:ℝ)≤L) (a : HeatCircle) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖≤R) :
    (∫⁻ s, rowEnergy G (U s) a ((T:ℝ)-(s:ℝ)) ∂timeMeasure H)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*constant L^(1+(β:ℝ)))*
        stateFactor R β*ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/2)/((1-(β:ℝ))/2)) := by
  have hbr : (β:ℝ)<1 := by exact_mod_cast hβ
  have hc := constant_nonneg (T.property.trans hTL)
  have hh := integrate_rate_until (fun u r ↦ rowEnergy G u a r) (β := β)
    (K := 2*(‖G 0‖+(C:ℝ))^2*constant L^(1+(β:ℝ)))
    (α := -(1+(β:ℝ))/2)
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hc _)) (by linarith)
    (fun u r hr ↦ by simp only [rowEnergy, dite_eq_right (not_lt_of_ge hr)])
    (fun u r hr hrT ↦ by
      simpa only [rowEnergy, dite_eq_left hr] using coefficient_energy hG hβ.le u hr hrT a)
    T H hTH hTL U hU
  simpa only [show -(1+(β:ℝ))/2+1=(1-(β:ℝ))/2 by ring] using hh

theorem row_bound {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β<1)
    (T H : ℝ≥0) (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖≤R) :
    (∫⁻ s, rowEnergy G (U s) a ((T:ℝ)-(s:ℝ)) ∂timeMeasure H)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*constant (T:ℝ)^(1+(β:ℝ)))*
        stateFactor R β*ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/2)/((1-(β:ℝ))/2)) :=
  row_bound_until hG hβ T H hTH (T:ℝ) le_rfl a U hU

end SHEStochastic.SublinearHeatFiniteHorizon
