module

public import SHEStochastic.SublinearHeatTimeIncrement
public import SHEStochastic.SublinearHeatSpatialIncrement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.SublinearHeatIntegratedEnergy
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V]

def stateFactor (R : ℝ) (β : ℝ≥0) : ℝ≥0∞ := 1 + ENNReal.ofReal (R ^ 2) ^ (β : ℝ)

theorem state_factor_le {β : ℝ≥0} {R : ℝ}
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) (hu : ‖u‖ ≤ R) :
    1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ) ≤ stateFactor R β := by
  have hh := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg u) hu 2)
  exact add_le_add le_rfl (ENNReal.rpow_le_rpow hh β.property)

/-- A causal observation at T uses the same energy on every larger
native integration horizon. No extension of the driving noise is used. -/
theorem causal_integral_eq {A : Type*} {T H : ℝ≥0} (hTH : T ≤ H)
    (F : A → ℝ → ℝ≥0∞) (U : ℝ≥0 → A) (hzero : ∀ u r, r ≤ 0 → F u r = 0) :
    (∫⁻ s, F (U s) ((T : ℝ) - (s : ℝ)) ∂timeMeasure H) =
      ∫⁻ s, F (U s) ((T : ℝ) - (s : ℝ)) ∂timeMeasure T := by
  rw [← timeMeasure_restrict hTH, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem H] with s hs
  by_cases hst : s ≤ T
  · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 T from ⟨hs.1, hst⟩)]
  · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 T from fun hh ↦ hst hh.2)]
    have hst' : (T : ℝ) ≤ s := by exact_mod_cast (le_of_not_ge hst)
    exact hzero _ _ (sub_nonpos.mpr hst')

/-- One integration lemma is reused for the base row and both increments.
The state bound is only in spatial L², as provided by an L² stopping time. -/
theorem integrate_rate_until (F : Lp E 2 (haarAddCircle (T := 2 * Real.pi)) → ℝ → ℝ≥0∞)
    {β : ℝ≥0} {K α R L : ℝ} (hK : 0 ≤ K) (hα : -1 < α)
    (hzero : ∀ u r, r ≤ 0 → F u r = 0)
    (hF : ∀ u r, 0 < r → r ≤ L → F u r ≤
      ENNReal.ofReal (K * r ^ α) * (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)))
    (T H : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ L)
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖ ≤ R) :
    (∫⁻ s, F (U s) ((T : ℝ) - (s : ℝ)) ∂timeMeasure H) ≤
      ENNReal.ofReal K * stateFactor R β * ENNReal.ofReal ((T : ℝ) ^ (α + 1) / (α + 1)) := by
  rw [causal_integral_eq hTH F U hzero]
  have hmeas : timeMeasure T ≤ timeMeasure H := by
    rw [← timeMeasure_restrict hTH]
    exact Measure.restrict_le_self
  have hU : ∀ᵐ s ∂timeMeasure T, ‖U s‖ ≤ R := hU.filter_mono (ae_mono hmeas)
  have hb : ∀ᵐ s ∂timeMeasure T, F (U s) ((T : ℝ) - (s : ℝ)) ≤
      (ENNReal.ofReal K * stateFactor R β) * ENNReal.ofReal (((T : ℝ) - (s : ℝ)) ^ α) := by
    filter_upwards [hU] with s hs
    by_cases hr : 0 < (T : ℝ) - (s : ℝ)
    · have hr1 : (T : ℝ) - (s : ℝ) ≤ L := (sub_le_self _ s.property).trans hT
      calc
        _ ≤ ENNReal.ofReal (K * ((T : ℝ) - (s : ℝ)) ^ α) *
            (1 + ENNReal.ofReal (‖U s‖ ^ 2) ^ (β : ℝ)) := hF (U s) _ hr hr1
        _ ≤ ENNReal.ofReal (K * ((T : ℝ) - (s : ℝ)) ^ α) * stateFactor R β :=
          mul_le_mul_right (state_factor_le (U s) hs) _
        _ = _ := by rw [ENNReal.ofReal_mul hK]; ring
    · rw [hzero _ _ (le_of_not_gt hr)]
      exact zero_le
  calc
    _ ≤ ∫⁻ s, (ENNReal.ofReal K * stateFactor R β) *
        ENNReal.ofReal (((T : ℝ) - (s : ℝ)) ^ α) ∂timeMeasure T := lintegral_mono_ae hb
    _ = (ENNReal.ofReal K * stateFactor R β) *
        ∫⁻ s, ENNReal.ofReal (((T : ℝ) - (s : ℝ)) ^ α) ∂timeMeasure T :=
      lintegral_const_mul' _ _ (by dsimp [stateFactor]; finiteness)
    _ = _ := by rw [causal_rpow_mass hα T]

/-- Unit-time specialization retained for the existing local estimates. -/
theorem integrate_rate (F : Lp E 2 (haarAddCircle (T := 2 * Real.pi)) → ℝ → ℝ≥0∞)
    {β : ℝ≥0} {K α R : ℝ} (hK : 0 ≤ K) (hα : -1 < α)
    (hzero : ∀ u r, r ≤ 0 → F u r = 0)
    (hF : ∀ u r, 0 < r → r ≤ 1 → F u r ≤
      ENNReal.ofReal (K * r ^ α) * (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)))
    (T H : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1)
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖ ≤ R) :
    (∫⁻ s, F (U s) ((T : ℝ) - (s : ℝ)) ∂timeMeasure H) ≤
      ENNReal.ofReal K * stateFactor R β * ENNReal.ofReal ((T : ℝ) ^ (α + 1) / (α + 1)) :=
  integrate_rate_until F hK hα hzero hF T H hTH hT U hU

def rowEnergy (G : E → V) (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (a : HeatCircle) (r : ℝ) : ℝ≥0∞ :=
  if hr : 0 < r then ∫⁻ x, ENNReal.ofReal (‖kernel r hr a x‖ ^ 2 * ‖G (u x)‖ ^ 2) ∂haarAddCircle else 0

theorem row_bound {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β < 1)
    (T H : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖ ≤ R) :
    (∫⁻ s, rowEnergy G (U s) a ((T : ℝ) - (s : ℝ)) ∂timeMeasure H) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + (β : ℝ))) *
        stateFactor R β * ENNReal.ofReal ((T : ℝ) ^ ((1 - (β : ℝ)) / 2) / ((1 - (β : ℝ)) / 2)) := by
  have hbr : (β : ℝ) < 1 := by exact_mod_cast hβ
  have hc := ScaledHeatTraceEnvelope.constant_nonneg (M := 1) (scale := 2) (by norm_num) (by norm_num)
  have hh := integrate_rate (fun u r ↦ rowEnergy G u a r) (β := β)
    (K := 2 * (‖G 0‖ + (C : ℝ)) ^ 2 * ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + (β : ℝ)))
    (α := -(1 + (β : ℝ)) / 2) (by positivity) (by linarith)
    (fun u r hr ↦ by simp only [rowEnergy, dite_eq_right (not_lt_of_ge hr)])
    (fun u r hr hr1 ↦ by
      simpa only [rowEnergy, dite_eq_left hr] using SublinearHeatCoefficientEnergy.small_time_bound hG hβ.le u hr hr1 a)
    T H hTH hT U hU
  simpa only [show -(1 + (β : ℝ)) / 2 + 1 = (1 - (β : ℝ)) / 2 by ring] using hh

def timeEnergy (G : E → V) (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (a : HeatCircle) (δ : ℝ≥0) (r : ℝ) : ℝ≥0∞ :=
  if hr : 0 < r then ∫⁻ x, ENNReal.ofReal
    (‖kernel (r + δ) (add_pos_of_pos_of_nonneg hr δ.property) a x - kernel r hr a x‖ ^ 2 *
      ‖G (u x)‖ ^ 2) ∂haarAddCircle else 0

theorem time_bound {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β < 1)
    (T H : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a : HeatCircle) (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ 1) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖ ≤ R) :
    (∫⁻ s, timeEnergy G (U s) a δ ((T : ℝ) - (s : ℝ)) ∂timeMeasure H) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
        SublinearHeatTimeIncrement.smallTimeConstant ^ (1 + (β : ℝ)) * (δ : ℝ) ^ ((1 - (β : ℝ)) / 4)) *
          stateFactor R β * ENNReal.ofReal ((T : ℝ) ^ ((1 - (β : ℝ)) / 4) / ((1 - (β : ℝ)) / 4)) := by
  have hbr : (β : ℝ) < 1 := by exact_mod_cast hβ
  have hk : 0 ≤ SublinearHeatTimeIncrement.smallTimeConstant :=
    zero_le_one.trans SublinearHeatTimeIncrement.constant_ge_one
  have hh := integrate_rate (fun u r ↦ timeEnergy G u a δ r) (β := β)
    (K := 2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
      SublinearHeatTimeIncrement.smallTimeConstant ^ (1 + (β : ℝ)) * (δ : ℝ) ^ ((1 - (β : ℝ)) / 4))
    (α := -(3 + (β : ℝ)) / 4) (by positivity) (by linarith)
    (fun u r hr ↦ by simp only [timeEnergy, dite_eq_right (not_lt_of_ge hr)])
    (fun u r hr hr1 ↦ by
      simp only [timeEnergy, dite_eq_left hr]
      convert SublinearHeatTimeIncrement.holder_rate hG hβ.le u hr hr1 δ.property hδ a using 1 <;> rfl)
    T H hTH hT U hU
  simpa only [show -(3 + (β : ℝ)) / 4 + 1 = (1 - (β : ℝ)) / 4 by ring] using hh

def spatialEnergy (G : E → V) (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (a b : HeatCircle) (r : ℝ) : ℝ≥0∞ :=
  if hr : 0 < r then ∫⁻ x, ENNReal.ofReal
    (‖kernel r hr a x - kernel r hr b x‖ ^ 2 * ‖G (u x)‖ ^ 2) ∂haarAddCircle else 0

theorem spatial_bound {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : β < 1)
    (T H : ℝ≥0) (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a b : HeatCircle) {R : ℝ}
    (U : ℝ≥0 → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
    (hU : ∀ᵐ s ∂timeMeasure H, ‖U s‖ ≤ R) :
    (∫⁻ s, spatialEnergy G (U s) a b ((T : ℝ) - (s : ℝ)) ∂timeMeasure H) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
        SublinearHeatSpatialIncrement.smallTimeConstant ^ (1 + (β : ℝ)) *
          (‖unitCenter a - unitCenter b‖ ^ 2) ^ ((1 - (β : ℝ)) / 4)) * stateFactor R β *
            ENNReal.ofReal ((T : ℝ) ^ ((1 - (β : ℝ)) / 4) / ((1 - (β : ℝ)) / 4)) := by
  have hbr : (β : ℝ) < 1 := by exact_mod_cast hβ
  have hk : 0 ≤ SublinearHeatSpatialIncrement.smallTimeConstant :=
    zero_le_one.trans SublinearHeatSpatialIncrement.constant_bounds.1
  have hh := integrate_rate (fun u r ↦ spatialEnergy G u a b r) (β := β)
    (K := 2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
      SublinearHeatSpatialIncrement.smallTimeConstant ^ (1 + (β : ℝ)) *
        (‖unitCenter a - unitCenter b‖ ^ 2) ^ ((1 - (β : ℝ)) / 4))
    (α := -(3 + (β : ℝ)) / 4) (by positivity) (by linarith)
    (fun u r hr ↦ by simp only [spatialEnergy, dite_eq_right (not_lt_of_ge hr)])
    (fun u r hr hr1 ↦ by
      simpa only [spatialEnergy, dite_eq_left hr] using
        SublinearHeatSpatialIncrement.holder_rate hG hβ.le u hr hr1 a b)
    T H hTH hT U hU
  simpa only [show -(3 + (β : ℝ)) / 4 + 1 = (1 - (β : ℝ)) / 4 by ring] using hh

end SHEStochastic.SublinearHeatIntegratedEnergy
