module

public import SHEStochastic.SublinearHeatFiniteHorizon
public import SHEStochastic.HeatIncrementInterpolatedRate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.FiniteHorizonHeatIncrements
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open scoped NNReal ENNReal

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩

def timeConstant (L : ℝ) : ℝ := 1+SublinearHeatFiniteHorizon.constant L+
  2^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L

def spaceConstant (L : ℝ) : ℝ := 1+SublinearHeatFiniteHorizon.constant L+
  (HeatMarkov.localConstant^2+4)*(4*Real.pi^2)^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L

theorem time_constants {L : ℝ} (hL : 0≤L) : 1≤timeConstant L ∧
    SublinearHeatFiniteHorizon.constant L≤timeConstant L ∧
    2^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L≤timeConstant L := by
  have hc := SublinearHeatFiniteHorizon.constant_nonneg hL
  have hp : 0≤2^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L := by positivity
  unfold timeConstant
  exact ⟨by linarith, by linarith, by linarith⟩

theorem space_constants {L : ℝ} (hL : 0≤L) : 1≤spaceConstant L ∧
    SublinearHeatFiniteHorizon.constant L≤spaceConstant L ∧
    (HeatMarkov.localConstant^2+4)*(4*Real.pi^2)^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L≤spaceConstant L := by
  have hc := SublinearHeatFiniteHorizon.constant_nonneg hL
  have hp : 0≤(HeatMarkov.localConstant^2+4)*(4*Real.pi^2)^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L := by positivity
  unfold spaceConstant
  exact ⟨by linarith, by linarith, by linarith⟩

theorem time_cap {t L : ℝ} (ht : 0<t) (htL : t≤L) :
    SublinearHeatRows.cap t≤timeConstant L*t^(-(1/2:ℝ)) :=
  (SublinearHeatFiniteHorizon.cap_bound ht htL).trans
    (mul_le_mul_of_nonneg_right (time_constants (ht.le.trans htL)).2.1 (by positivity))

theorem space_cap {t L : ℝ} (ht : 0<t) (htL : t≤L) :
    SublinearHeatRows.cap t≤spaceConstant L*t^(-(1/2:ℝ)) :=
  (SublinearHeatFiniteHorizon.cap_bound ht htL).trans
    (mul_le_mul_of_nonneg_right (space_constants (ht.le.trans htL)).2.1 (by positivity))

theorem time_energy {t δ L : ℝ} (ht : 0<t) (htL : t≤L) (hδ : 0≤δ) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel (t+δ) (add_pos_of_pos_of_nonneg ht hδ) a x-kernel t ht a x‖^2) ∂haarAddCircle)≤
      ENNReal.ofReal (timeConstant L*δ^(1/4:ℝ)*t^(-(3/4:ℝ))) := by
  apply (SublinearHeatTimeIncrement.energy_bound ht hδ (by norm_num : (0:ℝ)≤1/8) (by norm_num) a).trans
  apply ENNReal.ofReal_le_ofReal
  change ((δ/(t/2))^(1/8:ℝ))^2*SublinearHeatRows.cap t≤_
  calc
    _ ≤ ((δ/(t/2))^(1/8:ℝ))^2*(SublinearHeatFiniteHorizon.constant L*t^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (SublinearHeatFiniteHorizon.cap_bound ht htL) (sq_nonneg _)
    _ = (2^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L)*δ^(1/4:ℝ)*t^(-(3/4:ℝ)) := HeatIncrementRateAlgebra.time_ratio ht hδ
    _ ≤ _ := by gcongr; exact (time_constants (ht.le.trans htL)).2.2

theorem space_energy {t L : ℝ} (ht : 0<t) (htL : t≤L) (a b : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x-kernel t ht b x‖^2) ∂haarAddCircle)≤
      ENNReal.ofReal (spaceConstant L*(‖unitCenter a-unitCenter b‖^2)^(1/4:ℝ)*t^(-(3/4:ℝ))) := by
  apply (SublinearHeatSpatialIncrement.energy_fractional ht a b).trans
  apply ENNReal.ofReal_le_ofReal
  let q := ‖unitCenter a-unitCenter b‖
  let B := HeatMarkov.localConstant^2+4
  have hq : 0≤q := norm_nonneg _
  have he : q^(1/2:ℝ)=(q^2)^(1/4:ℝ) := by
    rw [← Real.rpow_natCast_mul hq 2 (1/4:ℝ)]
    norm_num
  calc
    _ ≤ B*(SublinearHeatFiniteHorizon.constant L*t^(-(1/2:ℝ)))*(q/Real.sqrt (clock t))^(1/2:ℝ) := by
      gcongr
      exact SublinearHeatFiniteHorizon.cap_bound ht htL
    _ = B*((q/Real.sqrt (clock t))^(1/2:ℝ)*(SublinearHeatFiniteHorizon.constant L*t^(-(1/2:ℝ)))) := by ring
    _ = B*(((4*Real.pi^2)^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L)*q^(1/2:ℝ)*t^(-(3/4:ℝ))) := by
      rw [clock, HeatIncrementRateAlgebra.space_ratio (by positivity : 0<4*Real.pi^2) ht hq]
    _ = (B*(4*Real.pi^2)^(1/4:ℝ)*SublinearHeatFiniteHorizon.constant L)*q^(1/2:ℝ)*t^(-(3/4:ℝ)) := by ring
    _ ≤ spaceConstant L*q^(1/2:ℝ)*t^(-(3/4:ℝ)) := by gcongr; exact (space_constants (ht.le.trans htL)).2.2
    _ = _ := by rw [he]

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

theorem time_holder {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β≤1)
    (u : Lp E 2 (haarAddCircle (T := 2*Real.pi))) {t δ L : ℝ}
    (ht : 0<t) (htL : t≤L) (hδ : 0≤δ) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel (t+δ) (add_pos_of_pos_of_nonneg ht hδ) a x-kernel t ht a x‖^2*
      ‖G (u x)‖^2) ∂haarAddCircle)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*timeConstant L^(1+(β:ℝ))*
        δ^((1-(β:ℝ))/4)*t^(-(3+(β:ℝ))/4))*(1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by
  let h (x : HeatCircle) := ENNReal.ofReal (‖kernel (t+δ) (add_pos_of_pos_of_nonneg ht hδ) a x-kernel t ht a x‖^2)
  have hh : Measurable h := (((kernel (t+δ) (add_pos_of_pos_of_nonneg ht hδ) a).continuous.sub
    (kernel t ht a).continuous).norm.pow 2).measurable.ennreal_ofReal
  have hb : ∀ᵐ x ∂haarAddCircle, h x≤ENNReal.ofReal (4*(timeConstant L*t^(-(1/2:ℝ)))^2) := by
    filter_upwards [SublinearHeatRows.kernel_bound ht a,
      SublinearHeatRows.kernel_bound (add_pos_of_pos_of_nonneg ht hδ) a] with x hx hy
    have hc := SublinearHeatRows.cap_antitone ht (le_add_of_nonneg_right hδ)
    have hd : ‖kernel (t+δ) (add_pos_of_pos_of_nonneg ht hδ) a x-kernel t ht a x‖≤2*(timeConstant L*t^(-(1/2:ℝ))) :=
      (norm_sub_le _ _).trans (by linarith [time_cap ht htL])
    exact ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ (norm_nonneg _) hd 2).trans_eq (by ring))
  have hk : 0<timeConstant L := zero_lt_one.trans_le (time_constants (ht.le.trans htL)).1
  have hz := HeatIncrementInterpolatedRate.bound hG hβ1 u h hh.aemeasurable hk ht hδ hb (time_energy ht htL hδ a)
  simpa only [h, ENNReal.ofReal_mul (sq_nonneg _)] using hz

theorem space_holder {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β≤1)
    (u : Lp E 2 (haarAddCircle (T := 2*Real.pi))) {t L : ℝ}
    (ht : 0<t) (htL : t≤L) (a b : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖kernel t ht a x-kernel t ht b x‖^2*‖G (u x)‖^2) ∂haarAddCircle)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*4^(β:ℝ)*spaceConstant L^(1+(β:ℝ))*
        (‖unitCenter a-unitCenter b‖^2)^((1-(β:ℝ))/4)*t^(-(3+(β:ℝ))/4))*(1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by
  let h (x : HeatCircle) := ENNReal.ofReal (‖kernel t ht a x-kernel t ht b x‖^2)
  have hh : Measurable h := (((kernel t ht a).continuous.sub (kernel t ht b).continuous).norm.pow 2).measurable.ennreal_ofReal
  have hb : ∀ᵐ x ∂haarAddCircle, h x≤ENNReal.ofReal (4*(spaceConstant L*t^(-(1/2:ℝ)))^2) := by
    filter_upwards [SublinearHeatRows.kernel_bound ht a, SublinearHeatRows.kernel_bound ht b] with x hx hy
    have hd : ‖kernel t ht a x-kernel t ht b x‖≤2*(spaceConstant L*t^(-(1/2:ℝ))) :=
      (norm_sub_le _ _).trans (by linarith [space_cap ht htL])
    exact ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ (norm_nonneg _) hd 2).trans_eq (by ring))
  have hk : 0<spaceConstant L := zero_lt_one.trans_le (space_constants (ht.le.trans htL)).1
  have hz := HeatIncrementInterpolatedRate.bound hG hβ1 u h hh.aemeasurable hk ht (sq_nonneg _) hb (space_energy ht htL a b)
  simpa only [h, ENNReal.ofReal_mul (sq_nonneg _)] using hz

end SHEStochastic.FiniteHorizonHeatIncrements
