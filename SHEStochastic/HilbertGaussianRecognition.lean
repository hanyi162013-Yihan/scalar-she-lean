module

public import SHEStochastic.HilbertSimpleEnergyDefect
public import SHEStochastic.L2EnergyContinuity
public import SHEStochastic.HilbertSimpleTimeCut
public import Mathlib.Topology.Sequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertGaussianRecognition
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- A general predictable Hilbert row with deterministic squared norm
has the Gaussian characteristic expectation dictated by its time energy.
The actual native integral is used, and bounded initial-past weights are
retained through the simple-row density limit. -/
theorem weighted_formula_from_past (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ≥0) (haH : a ≤ H) (u : Lp C 2 ν)
    (hu : ∀ᵐ p ∂ν, p.1 ≤ a → u p = 0) (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1))
    (hprofile : ∀ᵐ p ∂ν, ‖u p‖ ^ 2 = q p.1)
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[F a] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) :
    CharacteristicL2.weightedExpectation φ (FiniteCylindricalIto.rawIntegral P.toCoordinates e u) =
      (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) * (∫ ω, φ ω ∂μ) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((HilbertSimpleInputs.embedding_dense (F := F) (μ := μ) (H := H) e) u)
  choose V hV using hv
  have horig : Filter.Tendsto (fun n ↦ HilbertSimpleInputs.embedding F μ H (V n))
      Filter.atTop (𝓝 u) := by simpa only [hV] using hlim
  let U (n : ℕ) := HilbertSimpleTimeCut.cut a haH (V n)
  have hlim' : Filter.Tendsto (fun n ↦ HilbertSimpleInputs.embedding F μ H (U n))
      Filter.atTop (𝓝 u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ HilbertSimpleTimeCut.embedding_cut_sub_le a haH (V n) u hu)
      (tendsto_iff_norm_sub_tendsto_zero.mp horig)
  let c : ℂ := (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) * (∫ ω, φ ω ∂μ)
  let z (n : ℕ) := CharacteristicL2.weightedExpectation φ
    (FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H (U n)))
  have hbound (n : ℕ) : ‖z n - c‖ ≤ (1 / 2 : ℝ) *
      ∫ p, |‖HilbertSimpleInputs.embedding F μ H (U n) p‖ ^ 2 - ‖u p‖ ^ 2| ∂ν := by
    have he := HilbertSimpleEnergyDefect.native_defect_from_past (U n) P e a
      (HilbertSimpleTimeCut.cut_starts_after a haH (V n)) q hq hq0 hqp φ hφ hφbound
    have herror : (∫ p, |‖HilbertSimpleInputs.embedding F μ H (U n) p‖ ^ 2 - q p.1| ∂ν) =
        ∫ p, |‖HilbertSimpleInputs.embedding F μ H (U n) p‖ ^ 2 - ‖u p‖ ^ 2| ∂ν := by
      apply integral_congr_ae
      filter_upwards [hprofile] with p hp
      change |‖HilbertSimpleInputs.embedding F μ H (U n) p‖ ^ 2 - q p.1| = _
      rw [hp]
    exact he.trans_eq (congrArg (fun x : ℝ ↦ (1 / 2 : ℝ) * x) herror)
  have herrorlim := L2EnergyContinuity.tendsto_integral_sub hlim'
  have hzero : Filter.Tendsto (fun n ↦ ‖z n - c‖) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) hbound (by
      simpa using tendsto_const_nhds.mul herrorlim)
  have hz : Filter.Tendsto z Filter.atTop
      (𝓝 (CharacteristicL2.weightedExpectation φ (FiniteCylindricalIto.rawIntegral P.toCoordinates e u))) :=
    ((CharacteristicL2.weightedExpectation_continuous φ
      (hφ.mono (F.le a)).aestronglyMeasurable hφbound).tendsto _).comp
      ((FiniteCylindricalIto.rawIntegral P.toCoordinates e).continuous.tendsto u |>.comp hlim')
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique (hz.sub_const c).norm hzero))

/-- Initial-time specialization. -/
theorem weighted_formula (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 ν) (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1))
    (hprofile : ∀ᵐ p ∂ν, ‖u p‖ ^ 2 = q p.1)
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[F 0] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) :
    CharacteristicL2.weightedExpectation φ (FiniteCylindricalIto.rawIntegral P.toCoordinates e u) =
      (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) * (∫ ω, φ ω ∂μ) := by
  have hu : ∀ᵐ p ∂ν, p.1 ≤ 0 → u p = 0 := by
    filter_upwards [FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
      (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hp hz
    exact False.elim ((not_le.mpr hp.1) hz)
  exact weighted_formula_from_past P e 0 zero_le u hu q hq hq0 hqp hprofile φ hφ hφbound

/-- The same full-past identity at every real frequency. -/
theorem weighted_frequency_from_past (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ≥0) (haH : a ≤ H) (u : Lp C 2 ν)
    (hu : ∀ᵐ p ∂ν, p.1 ≤ a → u p = 0) (q : ℝ≥0 → ℝ) (hq : Integrable q νt) (hq0 : ∀ r, 0 ≤ q r)
    (hqp : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1))
    (hprofile : ∀ᵐ p ∂ν, ‖u p‖ ^ 2 = q p.1)
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[F a] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1) (x : ℝ) :
    CharacteristicL2.weightedExpectation φ (x • FiniteCylindricalIto.rawIntegral P.toCoordinates e u) =
      (Real.exp (-(x ^ 2 * ∫ r, q r ∂νt) / 2) : ℂ) * (∫ ω, φ ω ∂μ) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hux : ∀ᵐ p ∂ν, p.1 ≤ a → (x • u : Lp C 2 ν) p = 0 := by
    filter_upwards [Lp.coeFn_smul x u, hu] with p hs hp ht
    rw [hs, Pi.smul_apply, hp ht, smul_zero]
  have hpx : ∀ᵐ p ∂ν, ‖(x • u : Lp C 2 ν) p‖ ^ 2 = x ^ 2 * q p.1 := by
    filter_upwards [Lp.coeFn_smul x u, hprofile] with p hs hp
    rw [hs, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hp]
  simpa only [map_smul, integral_const_mul] using weighted_formula_from_past P e a haH
    (x • u) hux (fun r ↦ x ^ 2 * q r) (hq.const_mul _) (fun r ↦ mul_nonneg (sq_nonneg _) (hq0 r))
    (stronglyMeasurable_const.mul hqp) hpx φ hφ hφbound

end SHEStochastic.HilbertGaussianRecognition
