/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The split-at-the-later-time proof is adapted from formal-mathfin,
3c41aee9bf2d9743f9e66b439f90d1635843d2d2, ItoIsometryAdapted.lean.
Here all inputs are derived from the paper's finite-horizon coordinate law,
and different coordinates retain their exact Kronecker covariance.
-/
module
public import SHEStochastic.BrownianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.BrownianCoordinates
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (W : ι → ℝ≥0 → Ω → ℝ)
  (hW : ∀ n (a : Fin n → ι), FiniteBrownianLawOn F μ H (fun i ↦ W (a i))
    (fun i j ↦ if a i = a j then 1 else 0))
include hW

private theorem integrable_bdd_two_increment (i j : ι)
    {φ : Ω → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C)
    (a b c d : ℝ≥0) (ha : a ≤ H) (hb : b ≤ H) (hc : c ≤ H) (hd : d ≤ H) :
    Integrable (fun ω ↦ φ ω * ((W i b ω - W i a ω) * (W j d ω - W j c ω))) μ := by
  have hi : MemLp (fun ω ↦ W i b ω - W i a ω) 2 μ :=
    (memLp_eval F μ H W hW i b hb 2 (by simp)).sub (memLp_eval F μ H W hW i a ha 2 (by simp))
  have hj : MemLp (fun ω ↦ W j d ω - W j c ω) 2 μ :=
    (memLp_eval F μ H W hW j d hd 2 (by simp)).sub (memLp_eval F μ H W hW j c hc 2 (by simp))
  exact (hi.integrable_mul hj).bdd_mul hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hC ω)

private theorem weighted_two_increment_ordered
    (hWa : ∀ i t, Measurable[F t] (W i t)) (i j : ι)
    (a t t' : ℝ≥0) (hat : a ≤ t) (htt' : t ≤ t') (ht'H : t' ≤ H)
    {φ : Ω → ℝ} (hφ : Measurable[F a] φ) {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C) :
    (∫ ω, φ ω * ((W i t ω - W i a ω) * (W j t' ω - W j a ω)) ∂μ) =
      (∫ ω, φ ω ∂μ) * (((t : ℝ) - a) * (if i = j then 1 else 0)) := by
  have htH := htt'.trans ht'H
  have haH := hat.trans htH
  have hφm : Measurable φ := hφ.mono (F.le a) le_rfl
  have hΦ : Measurable[F t] (fun ω ↦ φ ω * (W i t ω - W i a ω)) :=
    (hφ.mono (F.mono hat) le_rfl).mul
      ((hWa i t).sub ((hWa i a).mono (F.mono hat) le_rfl))
  have hzero := integral_adapted_mul_increment F μ H W hW j t t' htt' ht'H hΦ
  have hsum : (∫ ω, φ ω * ((W i t ω - W i a ω) * (W j t' ω - W j a ω)) ∂μ) =
      (∫ ω, φ ω * ((W i t ω - W i a ω) * (W j t ω - W j a ω)) ∂μ) +
        ∫ ω, (φ ω * (W i t ω - W i a ω)) * (W j t' ω - W j t ω) ∂μ := by
    have hcommon := integrable_bdd_two_increment F μ H W hW i j hφm hC a t a t haH htH haH htH
    have hcross := integrable_bdd_two_increment F μ H W hW i j hφm hC a t t t' haH htH htH ht'H
    have hcross' : Integrable (fun ω ↦ (φ ω * (W i t ω - W i a ω)) *
        (W j t' ω - W j t ω)) μ := by simpa only [mul_assoc] using hcross
    rw [← integral_add hcommon hcross']
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
  rw [hsum, hzero, add_zero, weighted_common_increment F μ H W hW i j a t hat htH hφ]

/-- Conditional covariance for unequal observation times, including
repeated noise coordinates. Every observation stays within H. -/
theorem weighted_two_increment
    (hWa : ∀ i t, Measurable[F t] (W i t)) (i j : ι)
    (a t t' : ℝ≥0) (hat : a ≤ t) (hat' : a ≤ t') (htH : t ≤ H) (ht'H : t' ≤ H)
    {φ : Ω → ℝ} (hφ : Measurable[F a] φ) {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C) :
    (∫ ω, φ ω * ((W i t ω - W i a ω) * (W j t' ω - W j a ω)) ∂μ) =
      (∫ ω, φ ω ∂μ) * ((((min t t' : ℝ≥0) : ℝ) - a) * (if i = j then 1 else 0)) := by
  rcases le_total t t' with h | h
  · rw [min_eq_left h]
    exact weighted_two_increment_ordered F μ H W hW hWa i j a t t' hat h ht'H hφ hC
  · rw [min_eq_right h]
    have he := weighted_two_increment_ordered F μ H W hW hWa j i a t' t hat' h htH hφ hC
    have hδ : (if j = i then (1 : ℝ) else 0) = (if i = j then 1 else 0) := by
      by_cases hij : i = j <;> simp [hij, Ne.symm]
    rw [hδ] at he
    rw [← he]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)

private theorem rectangle_pairing_ordered
    (hWa : ∀ i t, Measurable[F t] (W i t)) (i j : ι)
    {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : Measurable[F s] f) (hg : Measurable[F s'] g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') (htH : t ≤ H) (ht'H : t' ≤ H) (hss' : s ≤ s') :
    (∫ ω, (f ω * (W i t ω - W i s ω)) * (g ω * (W j t' ω - W j s' ω)) ∂μ) =
      (∫ ω, f ω * g ω ∂μ) *
        (max 0 (min (t : ℝ) t' - max (s : ℝ) s') * (if i = j then 1 else 0)) := by
  have hfg : Measurable[F s'] (fun ω ↦ f ω * g ω) :=
    (hf.mono (F.mono hss') le_rfl).mul hg
  have hfgm : Measurable (fun ω ↦ f ω * g ω) := hfg.mono (F.le s') le_rfl
  have hfgb : ∀ ω, |f ω * g ω| ≤ Cf * Cg := fun ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) ((abs_nonneg _).trans (hfb ω))
  have hmax : max (s : ℝ) s' = (s' : ℝ) := max_eq_right (by exact_mod_cast hss')
  rw [hmax]
  by_cases htle : t ≤ s'
  · have hχ : Measurable[F s'] (fun ω ↦ f ω * (W i t ω - W i s ω) * g ω) :=
      ((hf.mono (F.mono hss') le_rfl).mul
        (((hWa i t).mono (F.mono htle) le_rfl).sub
          ((hWa i s).mono (F.mono hss') le_rfl))).mul hg
    have hzero := integral_adapted_mul_increment F μ H W hW j s' t' hst' ht'H hχ
    have hlen : max (0 : ℝ) (min (t : ℝ) t' - s') = 0 :=
      max_eq_left (sub_nonpos.mpr ((min_le_left _ _).trans (by exact_mod_cast htle)))
    rw [hlen, zero_mul, mul_zero, ← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
  · have hstt : s' ≤ t := (lt_of_not_ge htle).le
    have hT1 : (∫ ω, f ω * g ω * ((W i s' ω - W i s ω) * (W j t' ω - W j s' ω)) ∂μ) = 0 := by
      have hχ : Measurable[F s'] (fun ω ↦ f ω * g ω * (W i s' ω - W i s ω)) :=
        hfg.mul ((hWa i s').sub ((hWa i s).mono (F.mono hss') le_rfl))
      have he := integral_adapted_mul_increment F μ H W hW j s' t' hst' ht'H hχ
      rw [← he]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hT2 := weighted_two_increment F μ H W hW hWa i j s' t t' hstt hst' htH ht'H hfg hfgb
    have hsum : (∫ ω, (f ω * (W i t ω - W i s ω)) * (g ω * (W j t' ω - W j s' ω)) ∂μ) =
        (∫ ω, f ω * g ω * ((W i s' ω - W i s ω) * (W j t' ω - W j s' ω)) ∂μ) +
          ∫ ω, f ω * g ω * ((W i t ω - W i s' ω) * (W j t' ω - W j s' ω)) ∂μ := by
      rw [← integral_add
        (integrable_bdd_two_increment F μ H W hW i j hfgm hfgb s s' s' t'
          (hst.trans htH) (hst'.trans ht'H) (hst'.trans ht'H) ht'H)
        (integrable_bdd_two_increment F μ H W hW i j hfgm hfgb s' t s' t'
          (hst'.trans ht'H) htH (hst'.trans ht'H) ht'H)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    rw [hsum, hT1, hT2, zero_add, NNReal.coe_min]
    rw [max_eq_right (sub_nonneg.mpr
      (le_min (by exact_mod_cast hstt) (by exact_mod_cast hst')))]

/-- Exact predictable-rectangle covariance for any two recognized noise
coordinates on the native finite interval. This is the isometry kernel
for the cylindrical construction; distinct coordinates pair to zero. -/
theorem rectangle_pairing
    (hWa : ∀ i t, Measurable[F t] (W i t)) (i j : ι)
    {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : Measurable[F s] f) (hg : Measurable[F s'] g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') (htH : t ≤ H) (ht'H : t' ≤ H) :
    (∫ ω, (f ω * (W i t ω - W i s ω)) * (g ω * (W j t' ω - W j s' ω)) ∂μ) =
      (∫ ω, f ω * g ω ∂μ) *
        (max 0 (min (t : ℝ) t' - max (s : ℝ) s') * (if i = j then 1 else 0)) := by
  rcases le_total s s' with h | h
  · exact rectangle_pairing_ordered F μ H W hW hWa i j hf hg hfb hgb hst hst' htH ht'H h
  · rw [show (fun ω ↦ (f ω * (W i t ω - W i s ω)) * (g ω * (W j t' ω - W j s' ω))) =
      (fun ω ↦ (g ω * (W j t' ω - W j s' ω)) * (f ω * (W i t ω - W i s ω))) by
        funext ω; ring,
      rectangle_pairing_ordered F μ H W hW hWa j i hg hf hgb hfb hst' hst ht'H htH h,
      min_comm (t' : ℝ) t, max_comm (s' : ℝ) s]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    · by_cases hij : i = j <;> simp [hij, Ne.symm]

end SHEStochastic.BrownianCoordinates
