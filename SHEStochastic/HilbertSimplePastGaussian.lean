module

public import SHEStochastic.HilbertSimpleGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertSimplePastGaussian
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FilteredSimplePartition HilbertSimplePartition HilbertSimpleGaussian

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

variable (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  (V : HilbertSimpleInputs.bounded (E := C) F H) (a : ℝ≥0)
  (hVa : ∀ p ∈ V.val.value.support, a ≤ p.1)

include hVa in
theorem coefficient_zero_before {k : ℕ} (hk : marshalPart F H V.val k < a) (ω : Ω) :
    marshalMult F H V.val k ω = 0 := by
  unfold marshalMult
  apply Finset.sum_eq_zero
  intro p hp
  rw [if_neg]
  exact fun h ↦ (not_le.mpr hk) ((hVa p hp).trans h.1)

include hVa in
theorem cellIntegral_zero_before {k : ℕ} (hk : marshalPart F H V.val k < a) :
    cellIntegral P e V k = 0 := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hi : HilbertSimpleInputs.embedding F μ H (cell V k) = 0 := by
    apply Lp.ext
    filter_upwards [HilbertSimpleInputs.embedding_ae F μ H (cell V k), Lp.coeFn_zero C 2 ν]
      with p hp hz
    rw [hp, hz]
    change (cell V k).val p.1 p.2 = 0
    simp only [cell, HilbertSimpleInputs.step_apply,
      coefficient_zero_before V a hVa hk p.2, Set.indicator_zero]
  unfold cellIntegral
  rw [hi, map_zero]

/-- Before the cut, the increment is zero, so the past may already
include time `a`; after the cut, this is the original cell filtration. -/
def pastGrid : Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := F (max a (marshalPart F H V.val k))
  mono' := fun _ _ h ↦ F.mono (max_le_max_left a (marshalPart_mono F H V.val V.property h))
  le' k := F.le _

@[simp] theorem pastGrid_apply (k : ℕ) :
    pastGrid V a k = F (max a (marshalPart F H V.val k)) := rfl

theorem partialSum_past_adapted :
    StronglyAdapted (pastGrid V a) (partialSum P e V 0) := by
  intro k
  have hMk : StronglyMeasurable[F (marshalPart F H V.val k)] (partialSum P e V 0 k) := by
    have hh := partialSum_adapted P e V 0 k
    rw [gridFiltration_apply, Nat.zero_add] at hh
    exact hh
  exact hMk.mono (F.mono (le_max_right _ _))

include hVa in
theorem conditional_past_increment (k : ℕ) :
    μ[fun ω ↦ Complex.exp
      (((partialSum P e V 0 (k + 1) ω - partialSum P e V 0 k ω : ℝ) : ℂ) * Complex.I)
        | pastGrid V a k] =ᵐ[μ]
      (fun ω ↦ (Real.exp (-HilbertSimpleGaussian.variance V k ω / 2) : ℂ)) := by
  by_cases hak : a ≤ marshalPart F H V.val k
  · rw [pastGrid_apply, max_eq_right hak]
    have hh := conditional_increment P e V 0 k
    rw [gridFiltration_apply, Nat.zero_add] at hh
    exact hh
  · have hk := lt_of_not_ge hak
    have hzero : cellVersion P e V k =ᵐ[μ] fun _ ↦ 0 := by
      have hz : (cellIntegral P e V k : Ω → ℝ) =ᵐ[μ] fun _ ↦ 0 := by
        rw [cellIntegral_zero_before P e V a hVa hk]
        exact Lp.coeFn_zero ℝ 2 μ
      exact (cellVersion_ae P e V k).symm.trans hz
    have hphase : (fun ω ↦ Complex.exp
        (((partialSum P e V 0 (k + 1) ω - partialSum P e V 0 k ω : ℝ) : ℂ) * Complex.I)) =ᵐ[μ]
        fun _ ↦ (1 : ℂ) := by
      filter_upwards [hzero] with ω hω
      rw [partialSum_increment, Nat.zero_add, hω]
      simp
    have hh := condExp_congr_ae (m := pastGrid V a k) hphase
    rw [condExp_const ((pastGrid V a).le k) (1 : ℂ)] at hh
    simpa only [HilbertSimpleGaussian.variance, coefficient_zero_before V a hVa hk,
      norm_zero, zero_pow two_ne_zero, mul_zero, neg_zero, zero_div,
      Real.exp_zero, Complex.ofReal_one] using hh

include hVa in
/-- The same finite-grid error estimate retains weights from any fixed
past time when the simple row starts after that time. No completeness or
right-continuity assumption on the filtration is added. -/
theorem weighted_defect_from_past (N : ℕ) (φ : Ω → ℂ)
    (hφ : StronglyMeasurable[F a] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1)
    (q : ℕ → ℝ) (hq : ∀ k, 0 ≤ q k) :
    ‖(∫ ω, φ ω * Complex.exp
      ((((∑ k ∈ Finset.range N, cellIntegral P e V k : Lp ℝ 2 μ) ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (Real.exp (-(∑ k ∈ Finset.range N, q k) / 2) : ℂ) * (∫ ω, φ ω ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N,
        ∫ ω, |HilbertSimpleGaussian.variance V k ω - q k| ∂μ := by
  have hφ0 : StronglyMeasurable[pastGrid V a 0] φ := by
    rw [pastGrid_apply, marshalPart_zero F H V.val V.property, max_eq_left (zero_le : 0 ≤ a)]
    exact hφ
  have hh := GaussianCharacteristicDefect.weighted_finite_steps_defect
    (pastGrid V a) φ hφ0 hφbound (partialSum P e V 0) (partialSum_past_adapted P e V a)
    (Filter.Eventually.of_forall fun ω ↦ by simp [partialSum])
    (HilbertSimpleGaussian.variance V) (variance_integrable V)
    (fun k ω ↦ mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)) q hq
    (conditional_past_increment P e V a hVa) N
  have ha : (∑ k ∈ Finset.range N, cellIntegral P e V k : Lp ℝ 2 μ) =ᵐ[μ]
      partialSum P e V 0 N := by
    simpa only [Nat.zero_add] using partialSum_ae P e V 0 N
  have he := integral_congr_ae (ha.mono fun ω hω ↦
    congrArg (fun x : ℝ ↦ φ ω * Complex.exp ((x : ℂ) * Complex.I)) hω)
  rw [he]
  exact hh

end SHEStochastic.HilbertSimplePastGaussian
