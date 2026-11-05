module

public import SHEStochastic.UnboundedGlobalIncrementEnergy
public import SHEStochastic.UnboundedHeatIncrementCaps

import all Mathlib.Analysis.RCLike.Basic
import all Mathlib.Basic.Real.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.UnboundedGlobalIncrementCaps
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeHeatSpan UnboundedHeatIncrementCaps
open UnboundedGlobalIncrementEnergy
open scoped NNReal ENNReal

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

def timeConstant (G : E → V) (C β : ℝ≥0) (R : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  (ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.timeConstant (H:ℝ)^(1+(β:ℝ)))*
    ENNReal.ofReal ((H:ℝ)^exponent β/exponent β)+
   ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*SublinearHeatFiniteHorizon.constant (H:ℝ)^(1+(β:ℝ)))*
    ENNReal.ofReal ((H:ℝ)^exponent β/(2*exponent β)))*SublinearHeatIntegratedEnergy.stateFactor R β

def spaceConstant (G : E → V) (C β : ℝ≥0) (R : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.spaceConstant (H:ℝ)^(1+(β:ℝ)))*
    SublinearHeatIntegratedEnergy.stateFactor R β*ENNReal.ofReal ((H:ℝ)^exponent β/exponent β)

theorem time_bound (G : E → V) (C β : ℝ≥0) (hβ : β<1) (R : ℝ) (H T δ : ℝ≥0)
    (hT : T≤H) (hδ : δ≤H) :
    timeCap G C β R H T δ≤timeConstant G C β R H*ENNReal.ofReal ((δ:ℝ)^exponent β) := by
  have hq := exponent_pos hβ
  have htq : (T:ℝ)^exponent β/exponent β≤(H:ℝ)^exponent β/exponent β :=
    div_le_div_of_nonneg_right (Real.rpow_le_rpow T.property (show (T:ℝ)≤H from hT) hq.le) hq.le
  have hdq := Real.rpow_le_rpow δ.property (show (δ:ℝ)≤H from hδ) hq.le
  have hd2q : (δ:ℝ)^(2*exponent β)/(2*exponent β)≤
      ((H:ℝ)^exponent β/(2*exponent β))*(δ:ℝ)^exponent β := by
    have he : (δ:ℝ)^(2*exponent β)=((δ:ℝ)^exponent β)^2 := by
      calc
        _ = (δ:ℝ)^(exponent β*(2:ℕ)) := by congr 1; norm_num; ring
        _ = _ := Real.rpow_mul_natCast δ.property (exponent β) 2
    have hprod : ((δ:ℝ)^exponent β)^2≤(H:ℝ)^exponent β*(δ:ℝ)^exponent β := by
      convert! mul_le_mul_of_nonneg_right hdq (Real.rpow_nonneg δ.property (exponent β)) using 1
      exact pow_two _
    rw [he]
    calc
      _ ≤ ((H:ℝ)^exponent β*(δ:ℝ)^exponent β)/(2*exponent β) :=
        div_le_div_of_nonneg_right hprod (by positivity)
      _ = _ := by ring
  have hK : 0≤FiniteHorizonHeatIncrements.timeConstant (H:ℝ) :=
    zero_le_one.trans (FiniteHorizonHeatIncrements.time_constants H.property).1
  have hA : 0≤2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.timeConstant (H:ℝ)^(1+(β:ℝ)) := by positivity
  have he : (1-(β:ℝ))/2=2*exponent β := by dsimp [exponent]; ring
  dsimp [timeCap,rowCap]
  rw [ENNReal.ofReal_mul hA,he]
  calc
    _ ≤ (ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.timeConstant (H:ℝ)^(1+(β:ℝ)))*
          ENNReal.ofReal ((δ:ℝ)^exponent β))*SublinearHeatIntegratedEnergy.stateFactor R β*
          ENNReal.ofReal ((H:ℝ)^exponent β/exponent β)+
        ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*SublinearHeatFiniteHorizon.constant (H:ℝ)^(1+(β:ℝ)))*
          SublinearHeatIntegratedEnergy.stateFactor R β*
            ENNReal.ofReal (((H:ℝ)^exponent β/(2*exponent β))*(δ:ℝ)^exponent β) :=
      add_le_add (mul_le_mul_right (ENNReal.ofReal_le_ofReal htq) _) (mul_le_mul_right (ENNReal.ofReal_le_ofReal hd2q) _)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0≤(H:ℝ)^exponent β/(2*exponent β))]
      dsimp [timeConstant]
      ring

theorem space_bound (G : E → V) (C β : ℝ≥0) (hβ : β<1) (R : ℝ) (H T : ℝ≥0)
    (hT : T≤H) (a b : HeatCircle) :
    spaceCap G C β R H T a b≤ spaceConstant G C β R H*
      ENNReal.ofReal (‖unitCenter a-unitCenter b‖^(2*exponent β)) := by
  have hq := exponent_pos hβ
  have htq : (T:ℝ)^exponent β/exponent β≤(H:ℝ)^exponent β/exponent β :=
    div_le_div_of_nonneg_right (Real.rpow_le_rpow T.property (show (T:ℝ)≤H from hT) hq.le) hq.le
  have hK : 0≤FiniteHorizonHeatIncrements.spaceConstant (H:ℝ) :=
    zero_le_one.trans (FiniteHorizonHeatIncrements.space_constants H.property).1
  have hA : 0≤2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.spaceConstant (H:ℝ)^(1+(β:ℝ)) := by positivity
  dsimp [spaceCap]
  rw [ENNReal.ofReal_mul hA, ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  calc
    _ ≤ (ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*FiniteHorizonHeatIncrements.spaceConstant (H:ℝ)^(1+(β:ℝ)))*
        ENNReal.ofReal (‖unitCenter a-unitCenter b‖^(2*exponent β)))*SublinearHeatIntegratedEnergy.stateFactor R β*
        ENNReal.ofReal ((H:ℝ)^exponent β/exponent β) := mul_le_mul_right (ENNReal.ofReal_le_ofReal htq) _
    _ = _ := by dsimp [spaceConstant]; ring

theorem constants_finite (G : E → V) (C β : ℝ≥0) (R : ℝ) (H : ℝ≥0) :
    timeConstant G C β R H<⊤ ∧ spaceConstant G C β R H<⊤ := by
  constructor <;> dsimp [timeConstant,spaceConstant,SublinearHeatIntegratedEnergy.stateFactor] <;> finiteness

end SHEStochastic.UnboundedGlobalIncrementCaps
