module

public import SHEStochastic.HilbertSimpleInputs
public import SHEStochastic.L2EnergyContinuity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeEnergy
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νp" => Measure.prod (MathFin.ItoIntegralCLM.timeMeasure_T H) μ

/-- Pathwise energy of the chosen predictable representative. -/
def energy (u : Lp C 2 νin) (ω : Ω) : ℝ := ∫ r, ‖u (r, ω)‖ ^ 2 ∂νt

/-- The pathwise L1 error of squared row norms controls every stopped
energy error simultaneously. -/
def deviation (u v : Lp C 2 νin) (ω : Ω) : ℝ :=
  ∫ r, |‖u (r, ω)‖ ^ 2 - ‖v (r, ω)‖ ^ 2| ∂νt

theorem product_memLp (u : Lp C 2 νin) : MemLp (fun p ↦ u p) 2 νp :=
  memLp_of_memLp_trim F.predictable_le_prod (Lp.memLp u)

theorem integrable (u : Lp C 2 νin) : Integrable (energy u) μ :=
  (product_memLp u).norm.integrable_sq.integral_prod_right

theorem stronglyMeasurable (u : Lp C 2 νin) : StronglyMeasurable (energy u) :=
  (((Lp.stronglyMeasurable u).mono F.predictable_le_prod).norm.pow 2).integral_prod_left'

theorem deviation_integrable (u v : Lp C 2 νin) : Integrable (deviation u v) μ :=
  (((product_memLp u).norm.integrable_sq).sub ((product_memLp v).norm.integrable_sq)).abs.integral_prod_right

theorem deviation_mean (u v : Lp C 2 νin) :
    (∫ ω, deviation u v ω ∂μ) = ∫ p, |‖u p‖ ^ 2 - ‖v p‖ ^ 2| ∂νin := by
  have hi := (((product_memLp u).norm.integrable_sq).sub ((product_memLp v).norm.integrable_sq)).abs
  calc
    _ = ∫ p, |‖u p‖ ^ 2 - ‖v p‖ ^ 2| ∂νp := (integral_prod_symm _ hi).symm
    _ = _ := integral_trim F.predictable_le_prod
      (by simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.pow_apply] using
        (((Lp.stronglyMeasurable u).norm.pow 2).sub
          ((Lp.stronglyMeasurable v).norm.pow 2)).norm)

theorem mean_eq (u : Lp C 2 νin) : (∫ ω, energy u ω ∂μ) = ‖u‖ ^ 2 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  calc
    _ = ∫ p, ‖u p‖ ^ 2 ∂νp :=
      (integral_prod_symm _ (product_memLp u).norm.integrable_sq).symm
    _ = ∫ p, ‖u p‖ ^ 2 ∂νin :=
      integral_trim F.predictable_le_prod ((Lp.stronglyMeasurable u).norm.pow 2)
    _ = _ := L2EnergyContinuity.norm_sq u

/-- Native predictable almost-everywhere representatives have the same
pathwise energy for almost every sample. -/
theorem energy_ae_of_ae (u : Lp C 2 νin) (f : ℝ≥0 × Ω → C) (h : u =ᵐ[νin] f) :
    energy u =ᵐ[μ] (fun ω ↦ ∫ r, ‖f (r, ω)‖ ^ 2 ∂νt) := by
  have hp : u =ᵐ[νp] f := ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) h
  have hs := (Measure.measurePreserving_swap (μ := μ)
    (ν := MathFin.ItoIntegralCLM.timeMeasure_T H)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact integral_congr_ae (hω.mono fun r hr ↦ congrArg (fun z : C ↦ ‖z‖ ^ 2) hr)

theorem integral_energy_sub_le (u v : Lp C 2 νin) :
    (∫ ω, |energy u ω - energy v ω| ∂μ) ≤
      ∫ p, |‖u p‖ ^ 2 - ‖v p‖ ^ 2| ∂νin := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hu := (product_memLp u).norm.integrable_sq
  have hv := (product_memLp v).norm.integrable_sq
  calc
    _ ≤ ∫ ω, ∫ r, |‖u (r, ω)‖ ^ 2 - ‖v (r, ω)‖ ^ 2| ∂νt ∂μ := by
      apply integral_mono_ae ((integrable u).sub (integrable v)).abs
        (hu.sub hv).abs.integral_prod_right
      filter_upwards [hu.prod_left_ae, hv.prod_left_ae] with ω huω hvω
      change |(∫ r, ‖u (r, ω)‖ ^ 2 ∂νt) - (∫ r, ‖v (r, ω)‖ ^ 2 ∂νt)| ≤ _
      rw [← integral_sub huω hvω]
      exact abs_integral_le_integral_abs
    _ = ∫ p, |‖u p‖ ^ 2 - ‖v p‖ ^ 2| ∂νp :=
      (integral_prod_symm _ (hu.sub hv).abs).symm
    _ = _ := integral_trim F.predictable_le_prod
      (by simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.pow_apply] using
        (((Lp.stronglyMeasurable u).norm.pow 2).sub
          ((Lp.stronglyMeasurable v).norm.pow 2)).norm)

/-- The time energy is continuous in L1 under native L2 approximation. -/
theorem integral_energy_sub_bound (u v : Lp C 2 νin) :
    (∫ ω, |energy u ω - energy v ω| ∂μ) ≤ ‖u - v‖ * (‖u‖ + ‖v‖) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (integral_energy_sub_le u v).trans (L2EnergyContinuity.integral_sub_le u v)

theorem tendsto_energy_sub {κ : Type*} {l : Filter κ} {u : κ → Lp C 2 νin} {v : Lp C 2 νin}
    (h : Filter.Tendsto u l (𝓝 v)) :
    Filter.Tendsto (fun k ↦ ∫ ω, |energy (u k) ω - energy v ω| ∂μ) l (𝓝 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
    (fun k ↦ integral_energy_sub_le (u k) v) (L2EnergyContinuity.tendsto_integral_sub h)

theorem tendstoInMeasure_energy {κ : Type*} {l : Filter κ}
    {u : κ → Lp C 2 νin} {v : Lp C 2 νin} (h : Filter.Tendsto u l (𝓝 v)) :
    TendstoInMeasure μ (fun k ↦ energy (u k)) l (energy v) := by
  have he (k : κ) : eLpNorm (energy (u k) - energy v) 1 μ =
      ENNReal.ofReal (∫ ω, |energy (u k) ω - energy v ω| ∂μ) := by
    have hi := (integrable (u k)).sub (integrable v)
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  simp only [he]
  simpa using ENNReal.tendsto_ofReal (tendsto_energy_sub h)

theorem tendstoInMeasure_deviation {κ : Type*} {l : Filter κ}
    {u : κ → Lp C 2 νin} {v : Lp C 2 νin} (h : Filter.Tendsto u l (𝓝 v)) :
    TendstoInMeasure μ (fun k ↦ deviation (u k) v) l (fun _ ↦ 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have he (k : κ) : eLpNorm (deviation (u k) v - (fun _ ↦ 0)) 1 μ =
      ENNReal.ofReal (∫ ω, deviation (u k) v ω ∂μ) := by
    have hi := deviation_integrable (u k) v
    rw [show (fun _ : Ω ↦ (0 : ℝ)) = (0 : Ω → ℝ) from rfl, sub_zero,
      eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω ↦
      Real.norm_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  simp only [he, deviation_mean]
  simpa using ENNReal.tendsto_ofReal (L2EnergyContinuity.tendsto_integral_sub h)

end SHEStochastic.NativeEnergy
