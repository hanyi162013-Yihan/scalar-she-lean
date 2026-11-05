module

public import SHEStochastic.HilbertSimplePastGaussian
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertSimpleEnergyDefect
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition HilbertSimplePartition HilbertSimpleGaussian

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

variable (V : HilbertSimpleInputs.bounded (E := C) F H)

omit V in
/-- A deterministic time profile has the same integral in the native
predictable measure as in the finite-horizon time measure. -/
theorem integral_time_profile (q : ℝ≥0 → ℝ) (hq : Integrable q νt)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1)) :
    (∫ p, q p.1 ∂ν) = ∫ r, q r ∂νt := by
  change (∫ p, q p.1 ∂((νt).prod μ).trim F.predictable_le_prod) = _
  rw [← integral_trim F.predictable_le_prod hqp, integral_prod _ (hq.comp_fst μ)]
  simp

/-- The conditional Gaussian HilbertSimpleGaussian.variance of a cell is its pathwise energy. -/
theorem variance_cell (k : ℕ) (ω : Ω) :
    HilbertSimpleGaussian.variance V k ω =
      ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)),
        ‖V.val r ω‖ ^ 2 ∂νt := by
  have hle := marshalPart_mono F H V.val V.property (Nat.le_succ k)
  have htH := marshalPart_le_T F H V.val V.property (k + 1)
  rw [HilbertSimpleGaussian.variance, NNReal.coe_sub hle, ← integral_cell_const _ _ hle htH,
    integral_indicator measurableSet_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  change ‖marshalMult F H V.val k ω‖ ^ 2 = ‖V.val r ω‖ ^ 2
  rw [marshalMult_eq_uncurry F H V.val V.property hr.1 hr.2 ω]

/-- Replacing a random cell HilbertSimpleGaussian.variance by the integral of a deterministic
HilbertSimpleGaussian.variance density costs at most the L1 error on that cell. -/
theorem cell_error (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (k : ℕ) (ω : Ω) :
    |HilbertSimpleGaussian.variance V k ω -
      ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)), q r ∂νt| ≤
      ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)),
        |‖V.val r ω‖ ^ 2 - q r| ∂νt := by
  rw [variance_cell V k ω, ← integral_sub (path_memLp V ω).norm.integrable_sq.integrableOn
    hq.integrableOn]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (μ := (νt).restrict
      (Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1))))
      (fun r ↦ ‖V.val r ω‖ ^ 2 - q r)

theorem total_error (q : ℝ≥0 → ℝ) (hq : Integrable q νt) {N : ℕ}
    (hN : marshalPart F H V.val N = H) (ω : Ω) :
    (∑ k ∈ Finset.range N, |HilbertSimpleGaussian.variance V k ω -
      ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)), q r ∂νt|) ≤
      ∫ r, |‖V.val r ω‖ ^ 2 - q r| ∂νt := by
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)),
          |‖V.val r ω‖ ^ 2 - q r| ∂νt :=
      Finset.sum_le_sum (fun k _ ↦ cell_error V q hq k ω)
    _ = _ := integral_partition V hN _ ((path_memLp V ω).norm.integrable_sq.sub hq).abs

/-- The finite-grid characteristic-function error is controlled in the
original predictable input measure, the norm used for the density limit. -/
theorem mean_total_error (q : ℝ≥0 → ℝ) (hq : Integrable q νt)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1)) {N : ℕ}
    (hN : marshalPart F H V.val N = H) :
    (∑ k ∈ Finset.range N, ∫ ω, |HilbertSimpleGaussian.variance V k ω -
      ∫ r in Set.Ioc (marshalPart F H V.val k) (marshalPart F H V.val (k + 1)), q r ∂νt| ∂μ) ≤
      ∫ p, |‖V.val p.1 p.2‖ ^ 2 - q p.1| ∂ν := by
  let f (p : ℝ≥0 × Ω) := |‖V.val p.1 p.2‖ ^ 2 - q p.1|
  have hVprod : MemLp (Function.uncurry ⇑V.val) 2 ((νt).prod μ) :=
    memLp_of_memLp_trim F.predictable_le_prod (HilbertSimpleInputs.memLp F μ H V.val)
  have hf : Integrable f ((νt).prod μ) := (hVprod.norm.integrable_sq.sub (hq.comp_fst μ)).abs
  have hfp : StronglyMeasurable[F.predictable] f := by
    simpa only [f, Pi.sub_apply, Pi.pow_apply, Function.uncurry, Real.norm_eq_abs] using
      ((V.val.isStronglyPredictable.norm.pow 2).sub hqp).norm
  have hi (k : ℕ) : Integrable (fun ω ↦ |HilbertSimpleGaussian.variance V k ω -
      ∫ r in Set.Ioc (marshalPart F H V.val k)
        (marshalPart F H V.val (k + 1)), q r ∂νt|) μ :=
    ((variance_integrable (μ := μ) V k).sub (integrable_const _)).abs
  rw [← integral_finset_sum _ (fun k _ ↦ hi k)]
  calc
    _ ≤ ∫ ω, ∫ r, f (r, ω) ∂νt ∂μ := by
      apply integral_mono (integrable_finsetSum _ (fun k _ ↦ hi k)) hf.integral_prod_right
      exact total_error V q hq hN
    _ = ∫ p, f p ∂(νt).prod μ := (integral_prod_symm f hf).symm
    _ = _ := integral_trim F.predictable_le_prod hfp

/-- The Gaussian defect for a simple input is bounded by its squared
row-norm error in precisely the native predictable L2 input measure.
The variance profile may be any deterministic nonnegative time function. -/
theorem native_defect_from_past {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ≥0) (hVa : ∀ p ∈ V.val.value.support, a ≤ p.1)
    (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1))
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[F a] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    ‖(∫ ω, φ ω * Complex.exp
      ((FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) ω : ℂ)
        * Complex.I) ∂μ) -
      (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) * (∫ ω, φ ω ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∫ p,
        |‖HilbertSimpleInputs.embedding F μ H V p‖ ^ 2 - q p.1| ∂ν := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let N := (marshalEndpoints F H V.val).card - 1
  have hN : marshalPart F H V.val N = H := marshalPart_card_sub_one F H V.val V.property
  let qk (k : ℕ) := ∫ r in Set.Ioc (marshalPart F H V.val k)
    (marshalPart F H V.val (k + 1)), q r ∂νt
  have hqk (k : ℕ) : 0 ≤ qk k := integral_nonneg hq0
  have hi : (∑ k ∈ Finset.range N, cellIntegral P e V k : Lp ℝ 2 μ) =
      FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) := by
    simpa only [map_sum, cellIntegral] using congrArg (FiniteCylindricalIto.rawIntegral P.toCoordinates e)
      (embedding_sum (μ := μ) V hN)
  have hsum : (∑ k ∈ Finset.range N, qk k) = ∫ r, q r ∂νt :=
    integral_partition V hN q hq
  have hh := HilbertSimplePastGaussian.weighted_defect_from_past P e V a hVa N φ hφ hφbound qk hqk
  simp only [Nat.zero_add, hi, hsum] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have he : (∫ p, |‖HilbertSimpleInputs.embedding F μ H V p‖ ^ 2 - q p.1| ∂ν) =
      ∫ p, |‖V.val p.1 p.2‖ ^ 2 - q p.1| ∂ν :=
    integral_congr_ae ((HilbertSimpleInputs.embedding_ae F μ H V).mono fun p hp ↦ by
      change |‖HilbertSimpleInputs.embedding F μ H V p‖ ^ 2 - q p.1| = _
      rw [hp]
      rfl)
  rw [he]
  exact mean_total_error V q hq hqp hN

/-- Initial-time specialization of the full-past simple-input bound. -/
theorem native_defect {ι : Type*} [Countable ι] [DecidableEq ι]
    (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1))
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[F 0] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    ‖(∫ ω, φ ω * Complex.exp
      ((FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V) ω : ℂ)
        * Complex.I) ∂μ) -
      (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) * (∫ ω, φ ω ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∫ p,
        |‖HilbertSimpleInputs.embedding F μ H V p‖ ^ 2 - q p.1| ∂ν :=
  native_defect_from_past V P e 0 (fun _ _ ↦ zero_le) q hq hq0 hqp φ hφ hφbound

end SHEStochastic.HilbertSimpleEnergyDefect
