module

public import SHEStochastic.NativeEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeCrossEnergy
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νprod" => Measure.prod (MathFin.ItoIntegralCLM.timeMeasure_T H) μ

def cross (v u : Lp C 2 νin) (ω : Ω) : ℝ :=
  ∫ r, inner ℝ (v (r, ω)) (u (r, ω)) ∂νt

theorem stronglyMeasurable (v u : Lp C 2 νin) : StronglyMeasurable (cross v u) := by
  have h : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ inner ℝ (v p) (u p)) :=
    ((Lp.stronglyMeasurable v).mono F.predictable_le_prod).inner
      ((Lp.stronglyMeasurable u).mono F.predictable_le_prod)
  exact h.integral_prod_left'

theorem product_integrable (v u : Lp C 2 νin) :
    Integrable (fun p ↦ inner ℝ (v p) (u p)) νprod := by
  apply ((NativeEnergy.product_memLp v).norm.integrable_mul (NativeEnergy.product_memLp u).norm).mono'
    (((Lp.stronglyMeasurable v).mono F.predictable_le_prod).inner
      ((Lp.stronglyMeasurable u).mono F.predictable_le_prod)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p ↦ abs_real_inner_le_norm _ _

theorem integrable (v u : Lp C 2 νin) : Integrable (cross v u) μ :=
  (product_integrable v u).integral_prod_right

theorem cross_sub (v w u : Lp C 2 νin) :
    cross (v - w) u =ᵐ[μ] (fun ω ↦ cross v u ω - cross w u ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let z : Lp C 2 νin := v - w
  have he : (fun p ↦ inner ℝ (z p) (u p)) =ᵐ[νin]
      (fun p ↦ inner ℝ (v p) (u p) - inner ℝ (w p) (u p)) := by
    filter_upwards [Lp.coeFn_sub v w] with p hp
    change inner ℝ ((v - w) p) (u p) = _
    rw [hp, Pi.sub_apply, inner_sub_left]
  have hrep : ∀ᵐ ω ∂μ, ∀ᵐ r ∂νt, inner ℝ (z (r, ω)) (u (r, ω)) =
      inner ℝ (v (r, ω)) (u (r, ω)) - inner ℝ (w (r, ω)) (u (r, ω)) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := Prod.instMeasurableSpace
    have hp := ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) he
    exact Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := μ)
      (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp)
  filter_upwards [hrep, (product_integrable v u).prod_left_ae, (product_integrable w u).prod_left_ae]
    with ω hr hv hw
  change (∫ r, inner ℝ (z (r, ω)) (u (r, ω)) ∂νt) = _
  rw [cross, cross, ← integral_sub hv hw]
  exact integral_congr_ae hr

theorem energy_combination (v u : Lp C 2 νin) (a : ℝ) :
    NativeEnergy.energy (a • v - u) =ᵐ[μ]
      (fun ω ↦ a ^ 2 * NativeEnergy.energy v ω + NativeEnergy.energy u ω - 2 * a * cross v u ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hrow : (a • v - u : Lp C 2 νin) =ᵐ[νin] (fun p ↦ a • v p - u p) := by
    filter_upwards [Lp.coeFn_sub (a • v) u, Lp.coeFn_smul a v] with p hs hm
    rw [hs, Pi.sub_apply, hm, Pi.smul_apply]
  have hE := NativeEnergy.energy_ae_of_ae _ _ hrow
  filter_upwards [hE, (NativeEnergy.product_memLp v).norm.integrable_sq.prod_left_ae,
    (NativeEnergy.product_memLp u).norm.integrable_sq.prod_left_ae,
    (product_integrable v u).prod_left_ae] with ω hEω hvω huω hcω
  rw [hEω]
  have he (r : ℝ≥0) : ‖a • v (r, ω) - u (r, ω)‖ ^ 2 =
      a ^ 2 * ‖v (r, ω)‖ ^ 2 + ‖u (r, ω)‖ ^ 2 - 2 * a * inner ℝ (v (r, ω)) (u (r, ω)) := by
    rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_left]
    ring
  simp_rw [he]
  have hsum : Integrable (fun r ↦ a ^ 2 * ‖v (r, ω)‖ ^ 2 + ‖u (r, ω)‖ ^ 2) νt := by
    convert (hvω.const_mul (a ^ 2)).add huω using 1
  rw [integral_sub hsum (hcω.const_mul (2 * a)),
    integral_add (hvω.const_mul (a ^ 2)) huω, integral_const_mul, integral_const_mul]
  rfl

theorem energy_combination_le (v u : Lp C 2 νin) (a : ℝ) :
    NativeEnergy.energy (a • v - u) ≤ᵐ[μ]
      (fun ω ↦ 2 * a ^ 2 * NativeEnergy.energy v ω + 2 * NativeEnergy.energy u ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hrow : (a • v - u : Lp C 2 νin) =ᵐ[νin] (fun p ↦ a • v p - u p) := by
    filter_upwards [Lp.coeFn_sub (a • v) u, Lp.coeFn_smul a v] with p hs hm
    rw [hs, Pi.sub_apply, hm, Pi.smul_apply]
  have hp := NativeEnergy.product_memLp (a • v - u)
  have hE := NativeEnergy.energy_ae_of_ae _ _ hrow
  have hprodrow : (a • v - u : Lp C 2 νin) =ᵐ[νprod] (fun p ↦ a • v p - u p) :=
    ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hrow
  have hi := (hp.norm.integrable_sq.congr
    (hprodrow.mono fun p h ↦ congrArg (fun z : C ↦ ‖z‖ ^ 2) h)).prod_left_ae
  filter_upwards [hE, hi, (NativeEnergy.product_memLp v).norm.integrable_sq.prod_left_ae,
    (NativeEnergy.product_memLp u).norm.integrable_sq.prod_left_ae] with ω hEω hiω hvω huω
  rw [hEω]
  calc
    _ ≤ ∫ r, 2 * a ^ 2 * ‖v (r, ω)‖ ^ 2 + 2 * ‖u (r, ω)‖ ^ 2 ∂νt := by
      apply integral_mono hiω ((hvω.const_mul _).add (huω.const_mul _))
      intro r
      have hb := norm_sub_le (a • v (r, ω)) (u (r, ω))
      have hnorm : ‖a • v (r, ω) - u (r, ω)‖ ^ 2 ≤
          (‖a • v (r, ω)‖ + ‖u (r, ω)‖) ^ 2 :=
        sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hb
      have ht : (‖a • v (r, ω)‖ + ‖u (r, ω)‖) ^ 2 ≤
          2 * ‖a • v (r, ω)‖ ^ 2 + 2 * ‖u (r, ω)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖a • v (r, ω)‖ - ‖u (r, ω)‖)]
      have hh := hnorm.trans ht
      simpa only [Pi.add_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_assoc] using hh
    _ = _ := by rw [integral_add (hvω.const_mul _) (huω.const_mul _),
      integral_const_mul, integral_const_mul]; rfl

end SHEStochastic.NativeCrossEnergy
