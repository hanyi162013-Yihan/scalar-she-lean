module

public import SHE.CovarianceEndpoint
public import SHE.ProfileVolterra
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Actual integrable physical-frame domination for profile parameter marks,
including observations whose target is the terminal time. -/
noncomputable section
namespace SHE.HeatRowWeighted
open Set MeasureTheory AddCircle Finset StoppedFourier ProfileVariance WordRecursion
  CovarianceMatrix CovarianceEndpoint
open scoped Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Domain := ℝ × HeatCircle

def sourceMeasure (s : ℝ) : Measure Domain :=
  (volume.restrict (Ioc 0 s)).prod (haarAddCircle (T := 2 * Real.pi))

theorem heatRow_vector_measurable {n : ℕ} (Z : Fin n → Observation) :
    Measurable (fun p : Domain => heatRow Z p.1 p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact Measurable.of_eval (heatRow_measurable Z)

theorem heatRow_norm_sq_integrable {n : ℕ} (Z : Fin n → Observation) {t : ℝ}
    (ht : ∀ i, t < (Z i).target) :
    Integrable (fun x : HeatCircle => ‖heatRow Z t x‖ ^ 2) haarAddCircle := by
  simpa only [EuclideanSpace.real_norm_sq_eq] using
    integrable_finsetSum univ (fun i _ => heatRow_square_integrable Z ht i)

theorem heatRow_norm_sq_mass {n : ℕ} (Z : Fin n → Observation) {t : ℝ}
    (ht : ∀ i, t < (Z i).target) :
    (∫ x : HeatCircle, ‖heatRow Z t x‖ ^ 2 ∂haarAddCircle) =
      ∑ i, ‖circleHeat ((Z i).target - t) (Z i).center‖ ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum univ (fun i _ => heatRow_square_integrable Z ht i)]
  exact sum_congr rfl (fun i _ => heatRow_square_mass Z ht i)

/-- Uniform original-target frame mass with the genuine integrable endpoint
singularity. No matrix inverse or conditioning constant occurs. -/
theorem heatRow_norm_sq_mass_le {n : ℕ} (Z : Fin n → Observation) {s t : ℝ}
    (hs1 : s ≤ 1) (ht : t ∈ Ioo 0 s) (hZ : ∀ i, s ≤ (Z i).target) :
    (∫ x : HeatCircle, ‖heatRow Z t x‖ ^ 2 ∂haarAddCircle) ≤
      (n : ℝ) * (1 + heatConstant) * (s - t) ^ (-(1 / 2 : ℝ)) := by
  have hst : 0 < s - t := sub_pos.mpr ht.2
  have hst1 : s - t ≤ 1 := by linarith [ht.1]
  rw [heatRow_norm_sq_mass Z (fun i => ht.2.trans_le (hZ i))]
  have hpoint (i : Fin n) : ‖circleHeat ((Z i).target - t) (Z i).center‖ ^ 2 ≤
      (1 + heatConstant) * (s - t) ^ (-(1 / 2 : ℝ)) := by
    have hrow := circleHeat_norm_sq_bound (sub_pos.mpr (ht.2.trans_le (hZ i))) (Z i).center
    have hpow := Real.rpow_le_rpow_of_nonpos hst
      (show s - t ≤ (Z i).target - t by linarith [hZ i]) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have hone : 1 ≤ (s - t) ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hst hst1 (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hpow heatConstant_pos.le
    nlinarith
  calc
    _ ≤ ∑ _i : Fin n, (1 + heatConstant) * (s - t) ^ (-(1 / 2 : ℝ)) :=
      sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The exact physical frame has finite time-space energy after multiplication
by every time weight of exponent greater than −1. This includes the coarse
canonical-profile derivative exponent `(β−2)/4`. -/
theorem weighted_heatRow_integrable {n : ℕ} (Z : Fin n → Observation)
    {s a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ha : -1 < a)
    (hZ : ∀ i, s ≤ (Z i).target) :
    Integrable (fun p : Domain => p.1 ^ a * ‖heatRow Z p.1 p.2‖ ^ 2) (sourceMeasure s) := by
  have hm : Measurable (fun p : Domain => p.1 ^ a * ‖heatRow Z p.1 p.2‖ ^ 2) :=
    ((real_rpow_measurable a).comp measurable_fst).mul
      ((heatRow_vector_measurable Z).norm.pow_const (2 : ℕ))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact (heatRow_norm_sq_integrable Z
      (fun i => (lt_of_le_of_ne ht.2 hts).trans_le (hZ i))).const_mul (t ^ a)
  · have hp : IntervalIntegrable (fun t : ℝ => t ^ a * (s - t) ^ (-(1 / 2 : ℝ))) volume 0 s := by
      simpa only [show a + 1 - 1 = a by ring,
        show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by ring] using
        positive_power_pair_intervalIntegrable (show 0 < a + 1 by linarith)
          (show (0 : ℝ) < 1 / 2 by norm_num) hs.le
    have hdom : Integrable (fun t : ℝ => ((n : ℝ) * (1 + heatConstant)) *
        (t ^ a * (s - t) ^ (-(1 / 2 : ℝ)))) (volume.restrict (Ioc 0 s)) := by
      change IntegrableOn (fun t : ℝ => ((n : ℝ) * (1 + heatConstant)) *
        (t ^ a * (s - t) ^ (-(1 / 2 : ℝ)))) (Ioc 0 s) volume
      exact (hp.const_mul ((n : ℝ) * (1 + heatConstant))).1
    apply hdom.mono'
      (hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    have ht' : t ∈ Ioo 0 s := ⟨ht.1, lt_of_le_of_ne ht.2 hts⟩
    have hrow := heatRow_norm_sq_mass_le Z hs1 ht' hZ
    have heq : (∫ x : HeatCircle, ‖t ^ a * ‖heatRow Z t x‖ ^ 2‖ ∂haarAddCircle) =
        t ^ a * (∫ x : HeatCircle, ‖heatRow Z t x‖ ^ 2 ∂haarAddCircle) := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))]
      exact integral_const_mul _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), heq]
    have he := mul_le_mul_of_nonneg_left hrow (Real.rpow_nonneg ht.1.le a)
    nlinarith only [he]

/-- The corresponding exact beta-type frame energy bound. -/
theorem weighted_heatRow_energy_le {n : ℕ} (Z : Fin n → Observation)
    {s a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ha : -1 < a)
    (hZ : ∀ i, s ≤ (Z i).target) :
    (∫ p : Domain, p.1 ^ a * ‖heatRow Z p.1 p.2‖ ^ 2 ∂sourceMeasure s) ≤
      (n : ℝ) * (1 + heatConstant) * ProfileVolterra.powerConstant a * s ^ (a + 1 / 2) := by
  have hi := weighted_heatRow_integrable Z hs hs1 ha hZ
  rw [sourceMeasure, integral_prod _ hi]
  have hc := ProfileVolterra.singular_convolution_bound ha hs (by norm_num : (0 : ℝ) ≤ 1)
    (real_rpow_measurable a) (fun t ht => Real.rpow_nonneg ht.1.le _) (fun _ _ => by simp)
  have hp : Integrable (fun t : ℝ => ((n : ℝ) * (1 + heatConstant)) *
      ((s - t) ^ (-(1 / 2 : ℝ)) * t ^ a)) (volume.restrict (Ioc 0 s)) := by
    change IntegrableOn (fun t : ℝ => ((n : ℝ) * (1 + heatConstant)) *
      ((s - t) ^ (-(1 / 2 : ℝ)) * t ^ a)) (Ioc 0 s) volume
    exact (hc.1.const_mul ((n : ℝ) * (1 + heatConstant))).1
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) s, ((n : ℝ) * (1 + heatConstant)) *
        ((s - t) ^ (-(1 / 2 : ℝ)) * t ^ a) := by
      apply integral_mono_ae hi.integral_prod_left hp
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
      have ht' : t ∈ Ioo 0 s := ⟨ht.1, lt_of_le_of_ne ht.2 hts⟩
      rw [integral_const_mul]
      have he := mul_le_mul_of_nonneg_left (heatRow_norm_sq_mass_le Z hs1 ht' hZ)
        (Real.rpow_nonneg ht.1.le a)
      nlinarith only [he]
    _ = ((n : ℝ) * (1 + heatConstant)) * (∫ t in (0 : ℝ)..s,
        (s - t) ^ (-(1 / 2 : ℝ)) * t ^ a) := by
      rw [← intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_const_mul]
    _ ≤ ((n : ℝ) * (1 + heatConstant)) *
        (1 * ProfileVolterra.powerConstant a * s ^ (a + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hc.2 (by positivity [heatConstant_pos])
    _ = _ := by ring

end SHE.HeatRowWeighted
