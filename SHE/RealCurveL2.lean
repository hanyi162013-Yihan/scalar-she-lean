module

public import SHE.MeasuredRealCurves
public import SHE.ProfileL2
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
set_option autoImplicit false

/-! Recovering sharp spatial L² derivative estimates from actual scalar
parameter derivatives and finite differences. A coarser pointwise domination
is used only to justify convergence, never as the final L² constant. -/
noncomputable section
namespace SHE.RealCurveL2
open Set MeasureTheory Filter ProfileL2
open scoped NNReal Topology

variable {X : Type*} [MeasurableSpace X]

def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem step_pos (n : ℕ) : 0 < step n := by unfold step; positivity

theorem step_tendsto : Tendsto step atTop (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  exact Eventually.of_forall (fun n => (step_pos n).ne')

def quotient (F : X → ℝ → ℝ) (θ : ℝ) (n : ℕ) (x : X) : ℝ :=
  (step n)⁻¹ * (F x (θ + step n) - F x θ)

theorem quotient_measurable {F : X → ℝ → ℝ} (hm : Measurable F.uncurry)
    (θ : ℝ) (n : ℕ) : Measurable (quotient F θ n) :=
  ((hm.comp (measurable_id.prodMk measurable_const)).sub
    (hm.comp (measurable_id.prodMk measurable_const))).const_mul _

omit [MeasurableSpace X] in
theorem quotient_bound {F : X → ℝ → ℝ} {K : ℝ≥0}
    (hlip : ∀ x, LipschitzWith K (F x)) (θ : ℝ) (n : ℕ) (x : X) :
    |quotient F θ n x| ≤ K := by
  have he := (hlip x).norm_sub_le (θ + step n) θ
  have hs : θ + step n - θ = step n := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hs, abs_of_pos (step_pos n)] at he
  calc
    _ = (step n)⁻¹ * |F x (θ + step n) - F x θ| := by
      rw [quotient, abs_mul, abs_inv, abs_of_pos (step_pos n)]
    _ ≤ (step n)⁻¹ * ((K : ℝ) * step n) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (step_pos n).le)
    _ = _ := by rw [mul_left_comm, inv_mul_cancel₀ (step_pos n).ne', mul_one]

omit [MeasurableSpace X] in
theorem quotient_tendsto {F : X → ℝ → ℝ} {θ : ℝ} {e : X → ℝ}
    (hd : ∀ x, HasDerivAt (F x) (e x) θ) (x : X) :
    Tendsto (fun n => quotient F θ n x) atTop (𝓝 (e x)) := by
  convert! (hd x).tendsto_slope_zero.comp step_tendsto using 1

/-- The sharp L² finite-difference constant transfers to the actual scalar
parameter derivative. The unrelated coarser pointwise Lipschitz constant only
supplies a finite dominated-convergence envelope. -/
theorem derivative_normTwo_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {F : X → ℝ → ℝ} {K : ℝ≥0} {D θ : ℝ}
    (hm : Measurable F.uncurry) (hlip : ∀ x, LipschitzWith K (F x))
    (_hD : 0 ≤ D)
    (hsharp : ∀ η ξ, normTwo μ (fun x => F x η - F x ξ) ≤ D * |η - ξ|)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (F x) (deriv (F x) θ) θ) :
    MemLp (fun x => deriv (F x) θ) 2 μ ∧
      normTwo μ (fun x => deriv (F x) θ) ≤ D := by
  have hemeas : Measurable (fun x => deriv (F x) θ) :=
    (MeasuredRealCurves.derivative_measurable (fun x => (hlip x).continuous) hm).comp
      (measurable_id.prodMk measurable_const)
  have heB : ∀ x, |deriv (F x) θ| ≤ (K : ℝ) := fun x => by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (hlip x)
  have hem := bounded_memLp (μ := μ) hemeas heB
  refine ⟨hem, ?_⟩
  have hq : ∀ n, MemLp (quotient F θ n) 2 μ := fun n =>
    bounded_memLp (quotient_measurable hm θ n) (quotient_bound hlip θ n)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => quotient F θ n x) atTop (𝓝 (deriv (F x) θ)) := by
    filter_upwards [hd] with x hx
    convert! hx.tendsto_slope_zero.comp step_tendsto using 1
  have hi := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : X => (K : ℝ) ^ 2)
    (fun n => ((quotient_measurable hm θ n).pow_const (2 : ℕ)).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hsquare := (sq_le_sq₀ (abs_nonneg _) K.2).mpr (quotient_bound hlip θ n x)
      rw [sq_abs] at hsquare
      convert! hsquare using 1))
    (hlim.mono (fun _ hx => hx.pow 2))
  have hn : Tendsto (fun n => normTwo μ (quotient F θ n)) atTop
      (𝓝 (normTwo μ (fun x => deriv (F x) θ))) := by
    exact (Real.continuous_sqrt.tendsto _).comp hi
  apply le_of_tendsto hn
  apply Eventually.of_forall
  intro n
  have hdif : MemLp (fun x => F x (θ + step n) - F x θ) 2 μ := by
    apply bounded_memLp (μ := μ) (C := (K : ℝ) * |θ + step n - θ|)
      ((hm.comp (measurable_id.prodMk measurable_const)).sub
        (hm.comp (measurable_id.prodMk measurable_const)))
    intro x
    change |F x (θ + step n) - F x θ| ≤ (K : ℝ) * |θ + step n - θ|
    have hb := (hlip x).norm_sub_le (θ + step n) θ
    simpa only [Real.norm_eq_abs] using hb
  rw [show quotient F θ n = fun x => (step n)⁻¹ * (F x (θ + step n) - F x θ) from rfl,
    normTwo_const_mul hdif, abs_inv, abs_of_pos (step_pos n)]
  have hs := hsharp (θ + step n) θ
  have hsub : θ + step n - θ = step n := by ring
  rw [hsub, abs_of_pos (step_pos n)] at hs
  calc
    _ ≤ (step n)⁻¹ * (D * step n) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (step_pos n).le)
    _ = D := by rw [mul_left_comm, inv_mul_cancel₀ (step_pos n).ne', mul_one]

end SHE.RealCurveL2
