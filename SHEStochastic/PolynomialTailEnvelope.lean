module

public import SHEStochastic.TailIntegralUniformity
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.PolynomialTailEnvelope
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {Ξ : Type*} [MeasurableSpace Ξ] (ρ : Measure Ξ) (g : Ξ → ℝ)

def initial (t : ℝ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun r => ρ {ω | r≤16*(g ω)^2}) t

def power (a t : ℝ) : ℝ≥0∞ :=
  (Ioi (16 : ℝ)).indicator (fun r => ENNReal.ofReal (r^(a/2))) t

/-- An integrable scalar-energy tail envelope: a bounded small-energy
part, the fixed initial L2-law tail, and an arbitrarily high polynomial
remainder supplied by the actual stochastic exit estimate. -/
def value (A : ℝ≥0∞) (a t : ℝ) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) 16).indicator (fun _ => (1 : ℝ≥0∞)) t+initial ρ g t+
    (A*ENNReal.ofReal ((2 : ℝ)^(-a)))*power a t

theorem initial_measurable : Measurable (initial ρ g) := by
  have h : Antitone (fun r : ℝ => ρ {ω | r≤16*(g ω)^2}) := by
    intro r s hrs
    exact measure_mono fun ω hω => hrs.trans hω
  exact h.measurable.indicator measurableSet_Ioi

theorem power_measurable (a : ℝ) : Measurable (power a) :=
  (measurable_id.pow_const (a/2)).ennreal_ofReal.indicator measurableSet_Ioi

theorem measurable (A : ℝ≥0∞) (a : ℝ) : Measurable (value ρ g A a) :=
  ((measurable_const.indicator measurableSet_Ioc).add (initial_measurable ρ g)).add
    ((power_measurable a).const_mul _)

theorem initial_finite (hg : Measurable g) (hL2 : MemLp g 2 ρ) : (∫⁻ t,initial ρ g t)≠⊤ := by
  have hn : ∀ ω,0≤16*(g ω)^2 := fun _ => by positivity
  have hm : Measurable (fun ω => 16*(g ω)^2) := (hg.pow_const 2).const_mul _
  have he := lintegral_eq_lintegral_meas_le ρ (Filter.Eventually.of_forall hn) hm.aemeasurable
  unfold initial
  rw [lintegral_indicator measurableSet_Ioi,←he]
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hn)).mpr (hL2.integrable_sq.const_mul 16)

theorem power_finite (a : ℝ) (ha : a < -2) : (∫⁻ t,power a t)≠⊤ := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : a/2 < -1) (by norm_num : (0 : ℝ)<16)
  unfold power
  rw [lintegral_indicator measurableSet_Ioi]
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (16 : ℝ)<t := ht
      exact Real.rpow_nonneg (by linarith : (0 : ℝ)≤t) _)).mpr hi

/-- Square-integrability of the fixed initial law is sufficient for
the full energy-tail envelope; no fourth initial moment is introduced. -/
theorem finite (hg : Measurable g) (hL2 : MemLp g 2 ρ)
    (A : ℝ≥0∞) (hA : A≠⊤) (a : ℝ) (ha : a < -2) : (∫⁻ t,value ρ g A a t)≠⊤ := by
  have hsmall : (∫⁻ t : ℝ,(Ioc (0 : ℝ) 16).indicator (fun _ => (1 : ℝ≥0∞)) t)≠⊤ := by
    rw [lintegral_indicator measurableSet_Ioc,lintegral_const,one_mul,Measure.restrict_apply_univ,Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hi := initial_finite ρ g hg hL2
  have hp := power_finite a ha
  unfold value
  rw [lintegral_add_left
      (f := fun t : ℝ => (Ioc (0 : ℝ) 16).indicator (fun _ => (1 : ℝ≥0∞)) t+initial ρ g t)
      ((measurable_const.indicator measurableSet_Ioc).add (initial_measurable ρ g)),
    lintegral_add_left
      (f := fun t : ℝ => (Ioc (0 : ℝ) 16).indicator (fun _ => (1 : ℝ≥0∞)) t)
      (measurable_const.indicator measurableSet_Ioc),
    lintegral_const_mul'' _ (power_measurable a).aemeasurable]
  finiteness

end SHEStochastic.PolynomialTailEnvelope
