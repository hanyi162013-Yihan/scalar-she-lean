module

public import SHEStochastic.HilbertGaussianLaw
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertGaussianVector
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

def combination {D : Type*} [AddCommMonoid D] [Module ℝ D] {n : ℕ}
    (S : Fin n → D) (x : EuclideanSpace ℝ (Fin n)) : D := ∑ i, x i • S i

theorem coe_combination {Z D : Type*} [MeasurableSpace Z] [NormedAddCommGroup D]
    [NormedSpace ℝ D] {ρ : Measure Z} {n : ℕ} (S : Fin n → Lp D 2 ρ)
    (x : EuclideanSpace ℝ (Fin n)) :
    combination S x =ᵐ[ρ] (fun p ↦ ∑ i, x i • S i p) := by
  have ha : ∀ᵐ p ∂ρ, ∀ i : Fin n, (x i • S i : Lp D 2 ρ) p = x i • S i p :=
    ae_all_iff.mpr (fun i ↦ Lp.coeFn_smul (x i) (S i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ x i • S i), ha] with p hs hp
  unfold combination
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ ↦ hp i)

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "ν" => FiniteScalarIto.inputMeasure F μ H

def nativeVector (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (S : Fin n → Lp C 2 ν) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i) ω)

/-- Matching a deterministic time-dependent Gram supplies all scalar
variance profiles at once. No stochastic theorem is assumed here. -/
theorem profiles_of_gram (S : Fin n → Lp C 2 ν) (D : Fin n → ℝ≥0 → C)
    (hD : ∀ i, MemLp (D i) 2 νt)
    (hDp : ∀ i, StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ D i p.1))
    (hGram : ∀ᵐ p ∂ν, ∀ i j, inner ℝ (S i p) (S j p) = inner ℝ (D i p.1) (D j p.1)) :
    ∀ x : EuclideanSpace ℝ (Fin n), ∃ q : ℝ≥0 → ℝ,
      Integrable q νt ∧ (∀ r, 0 ≤ q r) ∧
      StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1) ∧
      (∀ᵐ p ∂ν, ‖combination S x p‖ ^ 2 = q p.1) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  intro x
  let q (r : ℝ≥0) : ℝ := ‖∑ i, x i • D i r‖ ^ 2
  have hsum : MemLp (fun r ↦ ∑ i, x i • D i r) 2 νt := by
    exact memLp_finsetSum _ (fun i _ ↦ (hD i).const_smul (x i))
  have hsumPred : StronglyMeasurable[F.predictable]
      (fun p : ℝ≥0 × Ω ↦ ∑ i, x i • D i p.1) :=
    Finset.stronglyMeasurable_fun_sum _ (fun i _ ↦ (hDp i).const_smul (x i))
  refine ⟨q, hsum.norm.integrable_sq, (fun r ↦ sq_nonneg _), hsumPred.norm.pow 2, ?_⟩
  filter_upwards [coe_combination S x, hGram] with p hp hGp
  rw [hp]
  change ‖∑ i, x i • S i p‖ ^ 2 = ‖∑ i, x i • D i p.1‖ ^ 2
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hGp i j]

/-- Cramer--Wold assembly for the actual native integrals. The covariance
is their original input Gram, including singular and repeated rows.
The remaining hypothesis is deterministic time-profile bookkeeping. -/
theorem law_and_independent (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ≥0) (haH : a ≤ H) (S : Fin n → Lp C 2 ν)
    (hSa : ∀ i, ∀ᵐ p ∂ν, p.1 ≤ a → S i p = 0)
    (hprofiles : ∀ x : EuclideanSpace ℝ (Fin n), ∃ q : ℝ≥0 → ℝ,
      Integrable q νt ∧ (∀ r, 0 ≤ q r) ∧
      StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ q p.1) ∧
      (∀ᵐ p ∂ν, ‖combination S x p‖ ^ 2 = q p.1)) :
    HasLaw (nativeVector P e S) (multivariateGaussian 0 (gram ℝ S)) μ ∧
    Indep (MeasurableSpace.comap (nativeVector P e S)
      (borel (EuclideanSpace ℝ (Fin n)))) (F a) μ := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hX : Measurable (nativeVector P e S) :=
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr
      fun i ↦ (Lp.stronglyMeasurable (FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i))).measurable)
  apply ConditionalCharacteristic.law_and_independent (F a) (F.le a) hX
  intro x A hA
  obtain ⟨q, hq, hq0, hqp, hprofile⟩ := hprofiles x
  have hu : ∀ᵐ p ∂ν, p.1 ≤ a → combination S x p = 0 := by
    have hall := ae_all_iff.mpr hSa
    filter_upwards [coe_combination S x, hall] with p hp hpa htime
    rw [hp]
    exact Finset.sum_eq_zero (fun i _ ↦ by rw [hpa i htime, smul_zero])
  let φ : Ω → ℂ := A.indicator (fun _ ↦ 1)
  have hφ : StronglyMeasurable[F a] φ := stronglyMeasurable_const.indicator hA
  have hφbound (ω : Ω) : ‖φ ω‖ ≤ 1 := by
    by_cases hω : ω ∈ A
    · simp [φ, Set.indicator_of_mem hω]
    · simp [φ, Set.indicator_of_notMem hω]
  have hh := HilbertGaussianRecognition.weighted_formula_from_past P e a haH
    (combination S x) hu q hq hq0 hqp hprofile φ hφ hφbound
  change CharacteristicL2.weightedExpectation (A.indicator (fun _ ↦ (1 : ℂ))) _ = _ at hh
  rw [CharacteristicL2.weightedExpectation_indicator (F.le a _ hA)] at hh
  have hJ : FiniteCylindricalIto.rawIntegral P.toCoordinates e (combination S x) =
      combination (fun i ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i)) x := by
    simp only [combination, map_sum, map_smul]
  have hlinear : FiniteCylindricalIto.rawIntegral P.toCoordinates e (combination S x) =ᵐ[μ]
      (fun ω ↦ inner ℝ (nativeVector P e S ω) x) := by
    rw [hJ]
    filter_upwards [coe_combination (fun i ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i)) x] with ω hω
    rw [hω]
    simp only [nativeVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      WithLp.ofLp_toLp, Pi.star_apply, star_trivial, smul_eq_mul]
  have hQ : (∫ r, q r ∂νt) = ‖combination S x‖ ^ 2 := by
    calc
      _ = ∫ p, q p.1 ∂ν := (HilbertSimpleEnergyDefect.integral_time_profile q hq hqp).symm
      _ = ∫ p, ‖combination S x p‖ ^ 2 ∂ν := (integral_congr_ae hprofile).symm
      _ = _ := L2EnergyContinuity.norm_sq _
  have hquad : (x ⬝ᵥ (gram ℝ S) *ᵥ x : ℝ) = ‖combination S x‖ ^ 2 := by
    simpa only [star_trivial, combination, real_inner_self_eq_norm_sq] using
      star_dotProduct_gram_mulVec S (fun i ↦ x i) (fun i ↦ x i)
  have hchar : charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (gram ℝ S)) x =
      (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) := by
    rw [charFun_multivariateGaussian (posSemidef_gram ℝ S), hquad, hQ]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [neg_div]
  calc
    _ = CharacteristicL2.setExpectation A (FiniteCylindricalIto.rawIntegral P.toCoordinates e (combination S x)) :=
      integral_congr_ae ((hlinear.symm.mono fun ω hω ↦ congrArg
        (fun r : ℝ ↦ Complex.exp ((r : ℂ) * Complex.I)) hω).filter_mono ae_restrict_le)
    _ = (Real.exp (-(∫ r, q r ∂νt) / 2) : ℂ) * ∫ ω, φ ω ∂μ := hh
    _ = μ.real A • charFun (multivariateGaussian 0 (gram ℝ S)) x := by
      rw [hchar]
      dsimp only [φ]
      rw [integral_indicator (F.le a _ hA), setIntegral_const]
      simp only [Complex.real_smul, mul_one]
      ring

end SHEStochastic.HilbertGaussianVector
