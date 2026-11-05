module

public import SHE.CouplingLaws
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE
open MeasureTheory

/-- The elementary Hellinger bound in the entropy direction supplied
by the stopped stochastic exponential, namely `H(P | ZP)`. -/
theorem sqrt_density_entropy_bound {z : ℝ} (hz : 0 < z) :
    (Real.sqrt z - 1) ^ (2 : ℕ) ≤ -Real.log z + z - 1 := by
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hz)
  rw [Real.log_sqrt hz.le] at hlog
  nlinarith [Real.sq_sqrt hz.le]

section Density
variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A genuine strictly positive density of mean one has L1 deviation
controlled by its reverse entropy. The entropy estimate is an input;
the measure-comparison inequality is proved here. -/
theorem density_l1_le_sqrt_cost {Z : Ω → ℝ} {cost : ℝ}
    (hZpos : ∀ ω, 0 < Z ω) (hZ : Integrable Z μ) (hmean : (∫ ω, Z ω ∂μ) = 1)
    (hlog : Integrable (fun ω => Real.log (Z ω)) μ)
    (hcost : 0 ≤ cost) (hentropy : -(∫ ω, Real.log (Z ω) ∂μ) ≤ cost / 2) :
    (∫ ω, |Z ω - 1| ∂μ) ≤ 2 * Real.sqrt cost := by
  have hSmeas : AEStronglyMeasurable (fun ω => Real.sqrt (Z ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hZ.aestronglyMeasurable
  have hS : MemLp (fun ω => Real.sqrt (Z ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hSmeas).mpr
    simpa only [Real.sq_sqrt (hZpos _).le] using hZ
  have hSint : Integrable (fun ω => Real.sqrt (Z ω)) μ := hS.integrable (by norm_num)
  have hSmean : (∫ ω, Real.sqrt (Z ω) ∂μ) ≤ 1 := by
    have hh := mean_norm_le_sqrt_energy μ hS
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hZpos _).le,
      hmean, Real.sqrt_one] using hh
  have hD : MemLp (fun ω => Real.sqrt (Z ω) - 1) 2 μ := hS.sub (memLp_const 1)
  have hE : MemLp (fun ω => Real.sqrt (Z ω) + 1) 2 μ := hS.add (memLp_const 1)
  have hDsq := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  have hEsq := (memLp_two_iff_integrable_sq hE.aestronglyMeasurable).mp hE
  have hDenergy : (∫ ω, (Real.sqrt (Z ω)-1) ^ (2 : ℕ) ∂μ) ≤ cost / 2 := by
    calc
      _ ≤ ∫ ω, -Real.log (Z ω) + Z ω - 1 ∂μ :=
        integral_mono hDsq ((hlog.neg.add hZ).sub (integrable_const 1))
          (fun ω => sqrt_density_entropy_bound (hZpos ω))
      _ = -(∫ ω, Real.log (Z ω) ∂μ) := by
        have hi : Integrable (fun ω => -Real.log (Z ω) + Z ω) μ := hlog.neg.add hZ
        rw [integral_sub hi (integrable_const 1),
          integral_add (f := fun ω => -Real.log (Z ω)) (g := Z) hlog.neg hZ,
          integral_neg, hmean]
        simp
      _ ≤ _ := hentropy
  have hEenergy : (∫ ω, (Real.sqrt (Z ω)+1) ^ (2 : ℕ) ∂μ) ≤ 4 := by
    have heq : (fun ω => (Real.sqrt (Z ω)+1) ^ (2 : ℕ)) =
        (fun ω => Z ω + 2 * Real.sqrt (Z ω) + 1) := by
      funext ω
      nlinarith [Real.sq_sqrt (hZpos ω).le]
    have hi : Integrable (fun ω => Z ω + 2 * Real.sqrt (Z ω)) μ := hZ.add (hSint.const_mul 2)
    rw [heq, integral_add hi (integrable_const 1),
      integral_add (f := Z) (g := fun ω => 2 * Real.sqrt (Z ω)) hZ (hSint.const_mul 2),
      integral_const_mul, hmean]
    have hc : (∫ _ω : Ω, (1 : ℝ) ∂μ) = 1 := by simp
    rw [hc]
    linarith
  have hD' : MemLp (fun ω => Real.sqrt (Z ω)-1) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hD
  have hE' : MemLp (fun ω => Real.sqrt (Z ω)+1) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hE
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hD' hE'
  have hCS : (∫ ω, |Z ω-1| ∂μ) ≤
      Real.sqrt (∫ ω, (Real.sqrt (Z ω)-1) ^ (2 : ℕ) ∂μ) *
        Real.sqrt (∫ ω, (Real.sqrt (Z ω)+1) ^ (2 : ℕ) ∂μ) := by
    have hp : ∀ ω, ‖Real.sqrt (Z ω)-1‖ * ‖Real.sqrt (Z ω)+1‖ = |Z ω-1| := by
      intro ω
      rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt (hZpos ω).le]
    simp only [Real.rpow_two] at hholder
    simp only [hp] at hholder
    simpa only [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow] using hholder
  have hrootD := Real.sqrt_le_sqrt hDenergy
  have hrootE : Real.sqrt (∫ ω, (Real.sqrt (Z ω)+1) ^ (2 : ℕ) ∂μ) ≤ 2 := by
    calc
      _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hEenergy
      _ = 2 := by norm_num
  have hrootcost : Real.sqrt (cost/2) ≤ Real.sqrt cost := Real.sqrt_le_sqrt (by linarith)
  calc
    _ ≤ _ := hCS
    _ ≤ Real.sqrt (cost/2) * 2 := mul_le_mul hrootD hrootE (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ _ := by linarith

/-- Bounded tests of an actual density change are controlled by the
reverse-entropy estimate supplied by a stopped Girsanov exponential. -/
theorem density_test_bound {Z f : Ω → ℝ} {cost M : ℝ}
    (hZpos : ∀ ω, 0 < Z ω) (hZ : Integrable Z μ) (hmean : (∫ ω, Z ω ∂μ) = 1)
    (hlog : Integrable (fun ω => Real.log (Z ω)) μ)
    (hcost : 0 ≤ cost) (hentropy : -(∫ ω, Real.log (Z ω) ∂μ) ≤ cost / 2)
    (hf : AEStronglyMeasurable f μ) (hM : 0 ≤ M) (hfbound : ∀ ω, |f ω| ≤ M) :
    |(∫ ω, f ω ∂(μ.withDensity (fun ω => ENNReal.ofReal (Z ω)))) - (∫ ω, f ω ∂μ)| ≤
      2 * M * Real.sqrt cost := by
  have hfi : Integrable f μ := (integrable_const M).mono' hf
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hfbound ω)
  have hZfi : Integrable (fun ω => Z ω * f ω) μ := by
    apply (hZ.norm.const_mul M).mono' (hZ.aestronglyMeasurable.mul hf)
    filter_upwards with ω
    change ‖Z ω * f ω‖ ≤ M * ‖Z ω‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hfbound ω) (abs_nonneg (Z ω))
  have hZm : AEMeasurable (fun ω => ENNReal.ofReal (Z ω)) μ :=
    hZ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmap : (∫ ω, f ω ∂(μ.withDensity (fun ω => ENNReal.ofReal (Z ω)))) = ∫ ω, Z ω * f ω ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hZm
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hZpos _).le, smul_eq_mul]
  have hdeviation : Integrable (fun ω => |Z ω-1|) μ := by
    have hi : Integrable (fun ω => Z ω-1) μ := hZ.sub (integrable_const 1)
    simpa only [Real.norm_eq_abs] using hi.norm
  calc
    _ = |∫ ω, Z ω * f ω - f ω ∂μ| := by rw [hmap, integral_sub hZfi hfi]
    _ ≤ ∫ ω, |Z ω * f ω - f ω| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => Z ω * f ω - f ω)
    _ ≤ ∫ ω, M * |Z ω-1| ∂μ := by
      apply integral_mono (hZfi.sub hfi).norm (hdeviation.const_mul M)
      intro ω
      change |Z ω * f ω - f ω| ≤ M * |Z ω-1|
      have he : Z ω * f ω - f ω = (Z ω-1) * f ω := by ring
      rw [he, abs_mul]
      simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hfbound ω) (abs_nonneg (Z ω-1))
    _ = M * ∫ ω, |Z ω-1| ∂μ := integral_const_mul _ _
    _ ≤ 2 * M * Real.sqrt cost := by
      have hh := mul_le_mul_of_nonneg_left
        (density_l1_le_sqrt_cost μ hZpos hZ hmean hlog hcost hentropy) hM
      nlinarith only [hh]

/-- A bounded pair of tests agreeing outside an actual exceptional event
differs in expectation by its probability times twice the test bound. -/
theorem test_difference_of_agree_off_set {f g : Ω → ℝ} {M : ℝ} {B : Set Ω}
    (hB : MeasurableSet B) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (_hM : 0 ≤ M) (hfb : ∀ ω, |f ω| ≤ M) (hgb : ∀ ω, |g ω| ≤ M)
    (hagree : ∀ ω ∉ B, f ω = g ω) :
    |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)| ≤ 2 * M * μ.real B := by
  have hfi : Integrable f μ := (integrable_const M).mono' hf
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hfb ω)
  have hgi : Integrable g μ := (integrable_const M).mono' hg
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hgb ω)
  calc
    _ = |∫ ω, f ω-g ω ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |f ω-g ω| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => f ω-g ω)
    _ ≤ ∫ ω, B.indicator (fun _ => 2 * M) ω ∂μ := by
      apply integral_mono (hfi.sub hgi).norm ((integrable_const (2*M)).indicator hB)
      intro ω
      change |f ω-g ω| ≤ B.indicator (fun _ => 2*M) ω
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]
        exact (abs_sub _ _).trans (by linarith [hfb ω, hgb ω])
      · rw [Set.indicator_of_notMem hω, hagree ω hω, sub_self, abs_zero]
    _ = 2 * M * μ.real B := by rw [integral_indicator_const _ hB]; simp [mul_comm]

/-- The complete stopped measure-comparison bound used by the final
coupling argument. Only the density's mean/entropy and the exceptional
event estimate remain as standard stochastic-calculus inputs. -/
theorem stopped_measure_comparison {Z f g : Ω → ℝ} {cost M : ℝ} {B : Set Ω}
    (hZpos : ∀ ω, 0 < Z ω) (hZ : Integrable Z μ) (hmean : (∫ ω, Z ω ∂μ) = 1)
    (hlog : Integrable (fun ω => Real.log (Z ω)) μ)
    (hcost : 0 ≤ cost) (hentropy : -(∫ ω, Real.log (Z ω) ∂μ) ≤ cost / 2)
    (hB : MeasurableSet B) (hBcost : μ.real B ≤ cost)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hM : 0 ≤ M) (hfb : ∀ ω, |f ω| ≤ M) (hgb : ∀ ω, |g ω| ≤ M)
    (hagree : ∀ ω ∉ B, f ω = g ω) :
    |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂(μ.withDensity (fun ω => ENNReal.ofReal (Z ω))))| ≤
      2 * M * (Real.sqrt cost + cost) := by
  have hfirst := test_difference_of_agree_off_set μ hB hf hg hM hfb hgb hagree
  have hsecond := density_test_bound μ hZpos hZ hmean hlog hcost hentropy hg hM hgb
  calc
    _ ≤ |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)| +
      |(∫ ω, g ω ∂μ) - (∫ ω, g ω ∂(μ.withDensity (fun ω => ENNReal.ofReal (Z ω))))| := abs_sub_le _ _ _
    _ ≤ 2 * M * μ.real B + 2 * M * Real.sqrt cost := by
      rw [abs_sub_comm] at hsecond
      exact add_le_add hfirst hsecond
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hBcost (by positivity : 0 ≤ 2 * M)]

end Density
end SHE
