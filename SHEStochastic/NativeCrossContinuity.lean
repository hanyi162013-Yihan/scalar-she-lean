module

public import SHEStochastic.NativeCrossEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeCrossContinuity
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νprod" => Measure.prod (MathFin.ItoIntegralCLM.timeMeasure_T H) μ

/-- Ordinary time pairing is continuous from predictable L² to sample L¹.
This permits change-of-integral limits without a stronger moment assumption. -/
theorem integral_abs_le (v u : Lp C 2 νin) :
    (∫ ω, |NativeCrossEnergy.cross v u ω| ∂μ) ≤ ‖v‖ * ‖u‖ := by
  have hi := NativeCrossEnergy.product_integrable v u
  have hn := (NativeEnergy.product_memLp v).norm.integrable_mul (NativeEnergy.product_memLp u).norm
  calc
    _ ≤ ∫ ω, ∫ r, |inner ℝ (v (r, ω)) (u (r, ω))| ∂νt ∂μ := by
      apply integral_mono (NativeCrossEnergy.integrable v u).abs hi.abs.integral_prod_right
      intro ω
      exact abs_integral_le_integral_abs
    _ = ∫ p, |inner ℝ (v p) (u p)| ∂νprod := (integral_prod_symm _ hi.abs).symm
    _ ≤ ∫ p, ‖v p‖ * ‖u p‖ ∂νprod :=
      integral_mono hi.abs hn (fun p ↦ abs_real_inner_le_norm _ _)
    _ = ∫ p, ‖v p‖ * ‖u p‖ ∂νin :=
      integral_trim F.predictable_le_prod ((Lp.stronglyMeasurable v).norm.mul (Lp.stronglyMeasurable u).norm)
    _ ≤ ‖v‖ * ‖u‖ := by
      letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
      have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp v)
        (by simpa only [ENNReal.ofReal_ofNat] using Lp.memLp u)
      have he (w : Lp C 2 νin) :
          (∫ p, ‖w p‖ ^ (2 : ℝ) ∂νin) ^ (1 / (2 : ℝ)) = ‖w‖ := by
        rw [show (fun p ↦ ‖w p‖ ^ (2 : ℝ)) = (fun p ↦ ‖w p‖ ^ (2 : ℕ)) from
          funext fun p ↦ Real.rpow_two _, ← Real.sqrt_eq_rpow, L2EnergyContinuity.norm_sq,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      simpa only [he] using hh

theorem integral_abs_sub_le (v w u : Lp C 2 νin) :
    (∫ ω, |NativeCrossEnergy.cross v u ω - NativeCrossEnergy.cross w u ω| ∂μ) ≤
      ‖v - w‖ * ‖u‖ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  calc
    _ = ∫ ω, |NativeCrossEnergy.cross (v - w) u ω| ∂μ :=
      integral_congr_ae ((NativeCrossEnergy.cross_sub v w u).mono fun ω hω ↦ congrArg abs hω.symm)
    _ ≤ _ := integral_abs_le (v - w) u

theorem tendstoInMeasure {κ : Type*} {l : Filter κ} {v : κ → Lp C 2 νin}
    {w : Lp C 2 νin} (hv : Filter.Tendsto v l (𝓝 w)) (u : Lp C 2 νin) :
    TendstoInMeasure μ (fun k ↦ NativeCrossEnergy.cross (v k) u) l (NativeCrossEnergy.cross w u) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have he (k : κ) : eLpNorm (NativeCrossEnergy.cross (v k) u - NativeCrossEnergy.cross w u) 1 μ =
      ENNReal.ofReal (∫ ω, |NativeCrossEnergy.cross (v k) u ω - NativeCrossEnergy.cross w u ω| ∂μ) := by
    have hi := (NativeCrossEnergy.integrable (v k) u).sub (NativeCrossEnergy.integrable w u)
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  simp only [he]
  have ht := squeeze_zero (fun k ↦ integral_nonneg fun _ ↦ abs_nonneg _)
    (fun k ↦ integral_abs_sub_le (v k) w u)
    (by simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv).mul_const ‖u‖)
  simpa using ENNReal.tendsto_ofReal ht

end SHEStochastic.NativeCrossContinuity
