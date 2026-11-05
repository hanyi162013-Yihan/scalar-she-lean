module

public import SHEStochastic.UnboundedHeatSpatialMoments
public import SHEStochastic.UnboundedHeatTimeMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.UnboundedHeatIncrementCaps
open MeasureTheory SHE SHE.StoppedFourier SHE.NativeHeatSpan
open scoped NNReal ENNReal

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

def exponent (β : ℝ≥0) : ℝ := (1 - (β : ℝ)) / 4

theorem exponent_pos {β : ℝ≥0} (hβ : β < 1) : 0 < exponent β := by
  have h : (β : ℝ) < 1 := by exact_mod_cast hβ
  dsimp [exponent]
  linarith

def timeConstant (G : E → V) (C β : ℝ≥0) (R : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
    SublinearHeatTimeIncrement.smallTimeConstant ^ (1 + (β : ℝ))) *
      ENNReal.ofReal (1 / exponent β) +
    ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + (β : ℝ))) *
      ENNReal.ofReal (1 / (2 * exponent β))) * SublinearHeatIntegratedEnergy.stateFactor R β

def spatialConstant (G : E → V) (C β : ℝ≥0) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
    SublinearHeatSpatialIncrement.smallTimeConstant ^ (1 + (β : ℝ))) *
      SublinearHeatIntegratedEnergy.stateFactor R β * ENNReal.ofReal (1 / exponent β)

theorem time_bound (G : E → V) (C β : ℝ≥0) (hβ : β < 1) (R : ℝ) (T δ : ℝ≥0)
    (hT : (T : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ 1) :
    UnboundedHeatTimeMoments.energyCap G C β R T δ ≤
      timeConstant G C β R * ENNReal.ofReal ((δ : ℝ) ^ exponent β) := by
  have hq := exponent_pos hβ
  have hTq : (T : ℝ) ^ exponent β / exponent β ≤ 1 / exponent β :=
    div_le_div_of_nonneg_right (Real.rpow_le_one T.property hT hq.le) hq.le
  have hδq : (δ : ℝ) ^ (2 * exponent β) / (2 * exponent β) ≤
      (1 / (2 * exponent β)) * (δ : ℝ) ^ exponent β := by
    have hh := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge' δ.property hδ hq.le (by linarith : exponent β ≤ 2 * exponent β))
      (by positivity : 0 ≤ 2 * exponent β)
    simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul] at hh ⊢
    convert hh using 1 <;> rfl
  have hk : 0 ≤ SublinearHeatTimeIncrement.smallTimeConstant :=
    zero_le_one.trans SublinearHeatTimeIncrement.constant_ge_one
  have ht0 : 0 ≤ 2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
      SublinearHeatTimeIncrement.smallTimeConstant ^ (1 + (β : ℝ)) := by positivity
  have he : (1 - (β : ℝ)) / 2 = 2 * exponent β := by dsimp [exponent]; ring
  dsimp [UnboundedHeatTimeMoments.energyCap, UnboundedHeatFamily.energyCap]
  rw [ENNReal.ofReal_mul ht0, he]
  calc
    _ ≤ (ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
          SublinearHeatTimeIncrement.smallTimeConstant ^ (1 + (β : ℝ))) *
        ENNReal.ofReal ((δ : ℝ) ^ exponent β)) * SublinearHeatIntegratedEnergy.stateFactor R β *
          ENNReal.ofReal (1 / exponent β) +
        ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + (β : ℝ))) *
          SublinearHeatIntegratedEnergy.stateFactor R β *
            ENNReal.ofReal ((1 / (2 * exponent β)) * (δ : ℝ) ^ exponent β) := by
      exact add_le_add (mul_le_mul_right (ENNReal.ofReal_le_ofReal hTq) _)
        (mul_le_mul_right (ENNReal.ofReal_le_ofReal hδq) _)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * exponent β))]
      dsimp [timeConstant]
      ring

theorem spatial_bound (G : E → V) (C β : ℝ≥0) (hβ : β < 1) (R : ℝ) (T : ℝ≥0)
    (hT : (T : ℝ) ≤ 1) (a b : HeatCircle) :
    UnboundedHeatSpatialMoments.energyCap G C β R T a b ≤
      spatialConstant G C β R * ENNReal.ofReal (‖unitCenter a - unitCenter b‖ ^ (2 * exponent β)) := by
  have hq := exponent_pos hβ
  have hTq : (T : ℝ) ^ exponent β / exponent β ≤ 1 / exponent β :=
    div_le_div_of_nonneg_right (Real.rpow_le_one T.property hT hq.le) hq.le
  have hk : 0 ≤ SublinearHeatSpatialIncrement.smallTimeConstant :=
    zero_le_one.trans SublinearHeatSpatialIncrement.constant_bounds.1
  have hs0 : 0 ≤ 2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
      SublinearHeatSpatialIncrement.smallTimeConstant ^ (1 + (β : ℝ)) := by positivity
  dsimp [UnboundedHeatSpatialMoments.energyCap]
  rw [ENNReal.ofReal_mul hs0, ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  calc
    _ ≤ (ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
          SublinearHeatSpatialIncrement.smallTimeConstant ^ (1 + (β : ℝ))) *
        ENNReal.ofReal (‖unitCenter a - unitCenter b‖ ^ (2 * exponent β))) *
          SublinearHeatIntegratedEnergy.stateFactor R β * ENNReal.ofReal (1 / exponent β) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hTq) _
    _ = _ := by dsimp [spatialConstant]; ring

theorem constants_finite (G : E → V) (C β : ℝ≥0) (R : ℝ) :
    timeConstant G C β R < ⊤ ∧ spatialConstant G C β R < ⊤ := by
  constructor <;> dsimp [timeConstant, spatialConstant, SublinearHeatIntegratedEnergy.stateFactor] <;> finiteness

end SHEStochastic.UnboundedHeatIncrementCaps
