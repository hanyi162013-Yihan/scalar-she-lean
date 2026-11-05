module

public import SHE.GaussianItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Borel parameter dependence of the actual physical covariance and
Gaussian backward tests. Moving time limits are genuine integrals. -/
noncomputable section
namespace SHE.CovarianceFamilies
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion CovarianceMatrix ClippedCovariance GaussianContinuity GaussianConvolution
open scoped Matrix.Norms.Elementwise

abbrev State (n : ℕ) := WordRecursion.State n

variable {P : Type*} [MeasurableSpace P]

def densityFamily {n : ℕ} (c : P × (ℝ × HeatCircle) → ℝ) (Z : Fin n → Observation)
    (p : P × ℝ) (i j : Fin n) : ℝ := covarianceDensity (fun q => c (p.1, q)) Z p.2 i j

theorem densityFamily_measurable {n : ℕ} {c : P × (ℝ × HeatCircle) → ℝ}
    (hc : Measurable c) (Z : Fin n → Observation) (i j : Fin n) :
    Measurable (fun p => densityFamily c Z p i j) := by
  have hmap : Measurable (fun p : (P × ℝ) × HeatCircle => (p.1.1, (p.1.2, p.2))) := by fun_prop
  have hm : Measurable (fun p : (P × ℝ) × HeatCircle => c (p.1.1, (p.1.2, p.2)) *
      heatRow Z p.1.2 p.2 i * heatRow Z p.1.2 p.2 j) :=
    ((hc.comp hmap).mul ((heatRow_measurable Z i).comp (measurable_fst.snd.prodMk measurable_snd))).mul
      ((heatRow_measurable Z j).comp (measurable_fst.snd.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem clipped_covariance_measurable {n : ℕ} {c : P × (ℝ × HeatCircle) → ℝ}
    (hc : Measurable c) (Z : Fin n → Observation) {a b : ℝ} (hab : a ≤ b) :
    Measurable (fun p : P × ℝ => covariance (fun q => c (p.1, q)) Z (clip a b p.2) b) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hD := densityFamily_measurable hc Z i j
  have hs : MeasurableSet {p : (P × ℝ) × ℝ | clip a b p.1.2 < p.2 ∧ p.2 ≤ b} :=
    (measurableSet_lt ((continuous_clip a b).measurable.comp measurable_fst.snd) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hm : Measurable (fun p : (P × ℝ) × ℝ =>
      if clip a b p.1.2 < p.2 ∧ p.2 ≤ b then densityFamily c Z (p.1.1, p.2) i j else 0) :=
    (hD.comp (measurable_fst.fst.prodMk measurable_snd)).ite hs measurable_const
  have hi := (hm.stronglyMeasurable.integral_prod_right (ν := volume) (f := fun (p : P × ℝ) (t : ℝ) =>
    if clip a b p.2 < t ∧ t ≤ b then densityFamily c Z (p.1, t) i j else 0)).measurable
  convert hi using 1
  funext p
  change (∫ t in clip a b p.2..b, covarianceDensity (fun q => c (p.1, q)) Z t i j) = _
  rw [intervalIntegral.integral_of_le (clip_mem hab p.2).2]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Set.indicator, mem_Ioc, densityFamily]

theorem positive_clipped_covariance_measurable {n : ℕ} {c : P × (ℝ × HeatCircle) → ℝ}
    (hc : Measurable c) (Z : Fin n → Observation) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ p : P × ℝ, (covariance (fun q => c (p.1, q)) Z (clip a b p.2) b).PosSemidef) :
    Measurable (fun p : P × ℝ => (⟨covariance (fun q => c (p.1, q)) Z (clip a b p.2) b, hpos p⟩ : PositiveCovariance n)) :=
  (clipped_covariance_measurable hc Z hab).subtype_mk

theorem gaussian_family_measurable {n : ℕ} {C : P → PositiveCovariance n} (hC : Measurable C)
    {F : State n → ℝ} (hF : Continuous F) {M : ℝ} (hbound : ∀ z, ‖F z‖ ≤ M) :
    Measurable (fun p : P × State n => gaussianAverage (C p.1).val F p.2) := by
  have hc := continuous_gaussian_average (n := n) F hF hbound
  have hm := hc.measurable.comp ((hC.comp measurable_fst).prodMk measurable_snd)
  exact hm

theorem gaussian_hessian_family_measurable {n : ℕ} {C : P → PositiveCovariance n} (hC : Measurable C)
    {F : State n → ℝ} (hF : ContDiff ℝ 2 F) {M L B : ℝ}
    (hbound : ∀ z, ‖F z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z, ‖GaussianTaylor.hessian F z‖ ≤ B) :
    Measurable (fun p : P × State n => GaussianTaylor.hessian (gaussianAverage (C p.1).val F) p.2) := by
  have hc : Continuous (GaussianTaylor.hessian F) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  have hm := (continuous_gaussian_average (n := n) (GaussianTaylor.hessian F) hc hDD).measurable.comp
    ((hC.comp measurable_fst).prodMk measurable_snd)
  have heq : (fun p : P × State n => GaussianTaylor.hessian (gaussianAverage (C p.1).val F) p.2) =
      fun p => ∫ y : State n, GaussianTaylor.hessian F (p.2 + y) ∂multivariateGaussian 0 (C p.1).val := by
    funext p
    unfold GaussianTaylor.hessian
    rw [show gaussianAverage (C p.1).val F = GaussianSmooth.average (multivariateGaussian 0 (C p.1).val) F from rfl,
      GaussianSmooth.fderiv_fderiv_average _ hF hbound hD hDD]
    rfl
  rw [heq]
  exact hm

end SHE.CovarianceFamilies
