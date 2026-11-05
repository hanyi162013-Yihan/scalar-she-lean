module

public import SHEStochastic.FiniteHorizonHeatIncrements

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.FiniteHorizonIntegratedHeat
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open SublinearHeatIntegratedEnergy FiniteHorizonHeatIncrements
open scoped NNReal ENNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

theorem time_bound {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β<1)
    (T H : ℝ≥0) (hTH : T≤H) (a : HeatCircle) (δ : ℝ≥0) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖≤R) :
    (∫⁻ s, timeEnergy G (U s) a δ ((T:ℝ)-(s:ℝ)) ∂timeMeasure H)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*timeConstant (H:ℝ)^(1+(β:ℝ))*
        (δ:ℝ)^((1-(β:ℝ))/4))*stateFactor R β*ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/4)/((1-(β:ℝ))/4)) := by
  have hbr : (β:ℝ)<1 := by exact_mod_cast hβ
  have hK : 0≤timeConstant (H:ℝ) := zero_le_one.trans (time_constants H.property).1
  have hh := integrate_rate_until (fun u r ↦ timeEnergy G u a δ r) (β := β)
    (K := 2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*timeConstant (H:ℝ)^(1+(β:ℝ))*(δ:ℝ)^((1-(β:ℝ))/4))
    (α := -(3+(β:ℝ))/4) (by positivity) (by linarith)
    (fun u r hr ↦ by simp only [timeEnergy, dite_eq_right (not_lt_of_ge hr)])
    (fun u r hr hrH ↦ by
      convert! FiniteHorizonHeatIncrements.time_holder hG hβ.le u hr hrH δ.property a using 1
      simp only [timeEnergy, dite_eq_left hr]
      rfl)
    T H hTH (show (T:ℝ)≤H from hTH) U hU
  simpa only [show -(3+(β:ℝ))/4+1=(1-(β:ℝ))/4 by ring] using hh

theorem space_bound {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β<1)
    (T H : ℝ≥0) (hTH : T≤H) (a b : HeatCircle) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2*Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖≤R) :
    (∫⁻ s, spatialEnergy G (U s) a b ((T:ℝ)-(s:ℝ)) ∂timeMeasure H)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*spaceConstant (H:ℝ)^(1+(β:ℝ))*
        (‖unitCenter a-unitCenter b‖^2)^((1-(β:ℝ))/4))*stateFactor R β*
          ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/4)/((1-(β:ℝ))/4)) := by
  have hbr : (β:ℝ)<1 := by exact_mod_cast hβ
  have hK : 0≤spaceConstant (H:ℝ) := zero_le_one.trans (space_constants H.property).1
  have hh := integrate_rate_until (fun u r ↦ spatialEnergy G u a b r) (β := β)
    (K := 2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*spaceConstant (H:ℝ)^(1+(β:ℝ))*(‖unitCenter a-unitCenter b‖^2)^((1-(β:ℝ))/4))
    (α := -(3+(β:ℝ))/4) (by positivity) (by linarith)
    (fun u r hr ↦ by simp only [spatialEnergy, dite_eq_right (not_lt_of_ge hr)])
    (fun u r hr hrH ↦ by
      simpa only [spatialEnergy, dite_eq_left hr] using FiniteHorizonHeatIncrements.space_holder hG hβ.le u hr hrH a b)
    T H hTH (show (T:ℝ)≤H from hTH) U hU
  simpa only [show -(3+(β:ℝ))/4+1=(1-(β:ℝ))/4 by ring] using hh

end SHEStochastic.FiniteHorizonIntegratedHeat
