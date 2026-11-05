/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Adapted for an arbitrary Brownian filtration from formal-mathfin,
commit 3c41aee9bf2d9743f9e66b439f90d1635843d2d2, ItoIsometryAdapted.lean.
The shared-start pairing below uses only independence of each increment
from the full past sigma algebra, without assuming a natural filtration.
-/
module

public import MathFin.Foundations.ItoIsometryAdapted

@[expose] public section

namespace SHEStochastic.FilteredBrownianCore

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

/-- Measurability in the given filtration, including any additional past randomness. -/
def AdaptedAt (F : Filtration ℝ≥0 mΩ) (s : ℝ≥0) (φ : Ω → ℝ) : Prop :=
  Measurable[F s] φ

theorem AdaptedAt.measurable (_hBmeas : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {φ : Ω → ℝ} (hφ : AdaptedAt F s φ) : Measurable φ :=
  hφ.mono (F.le s) le_rfl

theorem AdaptedAt.mono {s t : ℝ≥0} (hst : s ≤ t) {φ : Ω → ℝ}
    (hφ : AdaptedAt F s φ) : AdaptedAt F t φ :=
  Measurable.mono hφ (F.mono hst) le_rfl

theorem AdaptedAt.mul {s : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt F s φ) (hψ : AdaptedAt F s ψ) :
    AdaptedAt F s (fun ω ↦ φ ω * ψ ω) := Measurable.mul hφ hψ

theorem AdaptedAt.sub {s : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt F s φ) (hψ : AdaptedAt F s ψ) :
    AdaptedAt F s (fun ω ↦ φ ω - ψ ω) := Measurable.sub hφ hψ

theorem adaptedAt_of_measurable (_hBmeas : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) : AdaptedAt F s φ := hφ

variable [hFB : IsFilteredPreBrownian B F μ]

include hFB

theorem adaptedAt_eval {s u : ℝ≥0} (hu : u ≤ s) : AdaptedAt F s (B u) :=
  (hFB.stronglyAdapted u).measurable.mono (F.mono hu) le_rfl

theorem adapted_indepFun_increment
    (_hBmeas : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : AdaptedAt F s φ) :
    IndepFun φ (fun ω ↦ B t ω - B s ω) μ := by
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le_left (hFB.indep s t hst).symm (Measurable.comap_le hφ)

variable (hB : IsPreBrownianReal B μ)

include hB

theorem integral_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : AdaptedAt F s φ) :
    ∫ ω, φ ω * (B t ω - B s ω) ∂μ = 0 := by
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas hst hφ
  rw [hindep.integral_fun_mul_eq_mul_integral (hφ.measurable hBmeas).aestronglyMeasurable
    ((hBmeas t).sub (hBmeas s)).aestronglyMeasurable]
  have hmean : ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
    have h := (hB.hasLaw_sub t s).integral_eq
    rwa [integral_id_gaussianReal] at h
  rw [hmean, mul_zero]

theorem integral_adapted_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {χ : Ω → ℝ} (hχ : AdaptedAt F s χ) :
    ∫ ω, χ ω * (B t ω - B s ω) ^ 2 ∂μ =
      (∫ ω, χ ω ∂μ) * ((t : ℝ) - s) := by
  have hindep := (adapted_indepFun_increment (μ := μ) hBmeas hst hχ).comp
    (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ ↦ x ^ 2) measurable_id (by fun_prop)
  have key := hindep.integral_fun_mul_eq_mul_integral
    (hχ.measurable hBmeas).aestronglyMeasurable
    (((hBmeas t).sub (hBmeas s)).pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply, id_eq] at key
  rw [key, MathFin.ItoIsometryAdapted.integral_increment_sq hB hst]

theorem integral_adapted_sq_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : AdaptedAt F s φ) :
    ∫ ω, (φ ω) ^ 2 * (B t ω - B s ω) ^ 2 ∂μ =
      (∫ ω, (φ ω) ^ 2 ∂μ) * ((t : ℝ) - s) :=
  integral_adapted_mul_increment_sq hB hBmeas hst (Measurable.pow_const hφ 2)

theorem memLp_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : AdaptedAt F s φ) (hφL2 : MemLp φ 2 μ) :
    MemLp (fun ω ↦ φ ω * (B t ω - B s ω)) 2 μ := by
  have hindep := (adapted_indepFun_increment (μ := μ) hBmeas hst hφ).comp
    (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2) (by fun_prop) (by fun_prop)
  have hΔsq : Integrable (fun ω ↦ (B t ω - B s ω) ^ 2) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_sq
  have hprod : Integrable (fun ω ↦ (φ ω) ^ 2 * (B t ω - B s ω) ^ 2) μ :=
    hindep.integrable_mul hφL2.integrable_sq hΔsq
  refine (memLp_two_iff_integrable_sq
    ((hφ.measurable hBmeas).mul ((hBmeas t).sub (hBmeas s))).aestronglyMeasurable).mpr ?_
  simpa [mul_pow] using hprod

omit hFB in
private lemma integrable_bdd_two_increment
    {h : Ω → ℝ} (hhm : Measurable h)
    {C : ℝ} (hhb : ∀ ω, |h ω| ≤ C) (a b c d : ℝ≥0) :
    Integrable (fun ω ↦ h ω * ((B b ω - B a ω) * (B d ω - B c ω))) μ := by
  have hprod : Integrable (fun ω ↦ (B b ω - B a ω) * (B d ω - B c ω)) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_mul
      (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two)
  exact hprod.bdd_mul hhm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hhb ω)

private theorem integral_adapted_two_increment_ordered
    (hBmeas : ∀ t, Measurable (B t)) {a t t' : ℝ≥0} (hat : a ≤ t) (htt' : t ≤ t')
    {χ : Ω → ℝ} (hχ : AdaptedAt F a χ) {C : ℝ} (hχb : ∀ ω, |χ ω| ≤ C) :
    ∫ ω, χ ω * ((B t ω - B a ω) * (B t' ω - B a ω)) ∂μ =
      (∫ ω, χ ω ∂μ) * ((t : ℝ) - a) := by
  have hχm := hχ.measurable hBmeas
  have hzero := integral_adapted_mul_increment hB hBmeas htt'
    ((hχ.mono hat).mul ((adaptedAt_eval (B := B) (μ := μ) le_rfl).sub
      (adaptedAt_eval (B := B) (μ := μ) hat)))
  have hsum : (∫ ω, χ ω * ((B t ω - B a ω) * (B t' ω - B a ω)) ∂μ) =
      (∫ ω, χ ω * (B t ω - B a ω) ^ 2 ∂μ) +
        ∫ ω, (χ ω * (B t ω - B a ω)) * (B t' ω - B t ω) ∂μ := by
    have hsquare := integrable_bdd_two_increment hB hχm hχb a t a t
    have hcross := integrable_bdd_two_increment hB hχm hχb a t t t'
    have hsquare' : Integrable (fun ω ↦ χ ω * (B t ω - B a ω) ^ 2) μ := by
      simpa only [pow_two] using hsquare
    have hcross' : Integrable (fun ω ↦ (χ ω * (B t ω - B a ω)) *
        (B t' ω - B t ω)) μ := by simpa only [mul_assoc] using hcross
    rw [← integral_add hsquare' hcross']
    exact integral_congr_ae (ae_of_all _ fun ω ↦ by ring)
  rw [hsum, hzero, add_zero, integral_adapted_mul_increment_sq hB hBmeas hat hχ]

/-- A full-past measurable coefficient factors out of the covariance of
two increments with the same start. Only one-increment independence is used. -/
theorem integral_adapted_two_increment
    (hBmeas : ∀ t, Measurable (B t)) {a t t' : ℝ≥0} (hat : a ≤ t) (hat' : a ≤ t')
    {χ : Ω → ℝ} (hχ : AdaptedAt F a χ) {C : ℝ} (hχb : ∀ ω, |χ ω| ≤ C) :
    ∫ ω, χ ω * ((B t ω - B a ω) * (B t' ω - B a ω)) ∂μ =
      (∫ ω, χ ω ∂μ) * (((min t t' : ℝ≥0) : ℝ) - a) := by
  rcases le_total t t' with h | h
  · rw [min_eq_left h]
    exact integral_adapted_two_increment_ordered hB hBmeas hat h hχ hχb
  · rw [min_eq_right h]
    rw [show (fun ω ↦ χ ω * ((B t ω - B a ω) * (B t' ω - B a ω))) =
      (fun ω ↦ χ ω * ((B t' ω - B a ω) * (B t ω - B a ω))) by
        funext ω; ring]
    exact integral_adapted_two_increment_ordered hB hBmeas hat' h hχ hχb

/-- Pairing identity, oriented case `s ≤ s'`. -/
private lemma rect_increment_pairing_aux
    (hBmeas : ∀ s, Measurable (B s)) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt F s f) (hg : AdaptedAt F s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (_hst : s ≤ t) (hst' : s' ≤ t') (hss' : s ≤ s') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  have hfm : Measurable f := hf.measurable hBmeas
  have hgm : Measurable g := hg.measurable hBmeas
  have hfg : AdaptedAt F s' (fun ω ↦ f ω * g ω) := (hf.mono hss').mul hg
  have hfgm : Measurable (fun ω ↦ f ω * g ω) := hfm.mul hgm
  have hfgb : ∀ ω, |f ω * g ω| ≤ Cf * Cg := fun ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb ω))
  have hmaxss' : max (s : ℝ) s' = (s' : ℝ) := max_eq_right (by exact_mod_cast hss')
  rw [hmaxss']
  by_cases htle : t ≤ s'
  · -- Disjoint intervals: the whole pairing is a forward increment with mean zero.
    have hχ : AdaptedAt F s' (fun ω ↦ f ω * (B t ω - B s ω) * g ω) :=
      ((hf.mono hss').mul ((adaptedAt_eval (B := B) (μ := μ) htle).sub (adaptedAt_eval (B := B) (μ := μ) hss'))).mul hg
    have h0 := integral_adapted_mul_increment hB hBmeas hst' hχ
    have hzero : max (0 : ℝ) ((min (t : ℝ) t') - s') = 0 := by
      refine max_eq_left ?_
      have : (min (t : ℝ) t') ≤ (s' : ℝ) :=
        le_trans (min_le_left _ _) (by exact_mod_cast htle)
      linarith
    rw [hzero, mul_zero, ← h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
  · -- Overlapping intervals: split the first increment at the later start `s'`.
    replace htle := not_le.mp htle
    have hT1 : ∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ = 0 := by
      have hχ : AdaptedAt F s' (fun ω ↦ f ω * g ω * (B s' ω - B s ω)) :=
        hfg.mul ((adaptedAt_eval (B := B) (μ := μ) le_rfl).sub (adaptedAt_eval (B := B) (μ := μ) hss'))
      have h0 := integral_adapted_mul_increment hB hBmeas hst' hχ
      rw [← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hT2 : ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω ∂μ) * (((min t t' : ℝ≥0) : ℝ) - s') :=
      integral_adapted_two_increment hB hBmeas htle.le hst' hfg hfgb
    have hsum : ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ)
          + ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ := by
      rw [← integral_add (integrable_bdd_two_increment hB hfgm hfgb s s' s' t')
                         (integrable_bdd_two_increment hB hfgm hfgb s' t s' t')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hcoe : ((min t t' : ℝ≥0) : ℝ) = min (t : ℝ) t' := by
      rcases le_total t t' with h | h
      · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
      · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
    rw [hsum, hT1, hT2, zero_add, hcoe]
    congr 1
    have h1 : (s' : ℝ) ≤ min (t : ℝ) t' :=
      le_min (by exact_mod_cast htle.le) (by exact_mod_cast hst')
    rw [max_eq_right (by linarith)]

/-- **Pairing identity for predictable rectangles.** For adapted bounded
integrands `f` (`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`,

with `vol((s,t] ∩ (s',t']) = max 0 (min t t' − max s s')`. The adapted
generalisation of the Wiener covariance identity, and the inner-product core of
the continuous Itô isometry. -/
theorem rect_increment_pairing
    (hBmeas : ∀ s, Measurable (B s)) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt F s f) (hg : AdaptedAt F s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  rcases le_total s s' with h | h
  · exact rect_increment_pairing_aux hB hBmeas hf hg hfb hgb hst hst' h
  · rw [show (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ)
          = ∫ ω, (g ω * (B t' ω - B s' ω)) * (f ω * (B t ω - B s ω)) ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring),
        rect_increment_pairing_aux hB hBmeas hg hf hgb hfb hst' hst h]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    · rw [min_comm (t' : ℝ) t, max_comm (s' : ℝ) s]


end SHEStochastic.FilteredBrownianCore
