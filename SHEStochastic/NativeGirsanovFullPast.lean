module

public import SHEStochastic.NativeGirsanovPastAlgebra
public import SHEStochastic.NativeExponentialSubprobability
public import SHEStochastic.ConditionalMGF

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeGirsanovFullPast
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open NativeExponential NativeGirsanovTilt

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

theorem conditional_mgf (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u v : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (hvs : ∀ᵐ p ∂νin, p.1 ≤ s → v p = 0)
    (q : ℝ) (hq : 0 ≤ q) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ q) (a : ℝ) :
    (measure P e u)[fun ω ↦ Real.exp (a * shift P e u v ω) | F s] =ᵐ[measure P e u]
      (fun _ ↦ Real.exp (a ^ 2 * q / 2)) := by
  letI : IsProbabilityMeasure (measure P e u) := probability P e u K hK hu
  have hI := (NativeGirsanovTilt.mgf P e u v K hK hu q hq hv a).1
  have hδI := (NativeExponentialSubprobability.integrable_and_le_one P e 1 (a • v - u)).1
  have hUI := (NativeExponentialSubprobability.integrable_and_le_one P e (-1) u).1
  have hCE := NativeGirsanovPastAlgebra.conditional_tilt_density P e s hsH u v a K hK hu hvs q hq hv
  have hset (A : Set Ω) (hA : MeasurableSet[F s] A) :
      (∫ ω in A, Real.exp (a * shift P e u v ω) ∂measure P e u) =
        ∫ _ in A, Real.exp (a ^ 2 * q / 2) ∂measure P e u := by
    have hδset : (∫ ω in A, density P e 1 (a • v - u) ω ∂μ) =
        ∫ ω in A, density P e (-1) u ω ∂μ := by
      calc
        _ = ∫ ω in A, μ[density P e 1 (a • v - u) | F s] ω ∂μ :=
          (setIntegral_condExp (F.le s) hδI hA).symm
        _ = ∫ ω in A, μ[density P e (-1) u | F s] ω ∂μ :=
          integral_congr_ae (ae_restrict_of_ae hCE)
        _ = _ := setIntegral_condExp (F.le s) hUI hA
    calc
      _ = ∫ ω in A, density P e (-1) u ω * Real.exp (a * shift P e u v ω) ∂μ :=
        setIntegral_change P e u _ A (F.le s _ hA)
      _ = Real.exp (a ^ 2 * q / 2) * ∫ ω in A, density P e 1 (a • v - u) ω ∂μ := by
        rw [integral_congr_ae (ae_restrict_of_ae (tilt_identity_of_energy P e u v a q hv)),
          integral_const_mul]
      _ = Real.exp (a ^ 2 * q / 2) * ∫ ω in A, density P e (-1) u ω ∂μ := by rw [hδset]
      _ = _ := by
        rw [setIntegral_change P e u _ A (F.le s _ hA), integral_mul_const]
        ring
  apply Filter.EventuallyEq.symm
  exact ae_eq_condExp_of_forall_setIntegral_eq (F.le s) hI
    (fun _ _ _ ↦ (integrable_const (Real.exp (a ^ 2 * q / 2))).integrableOn)
    (fun A hA _ ↦ (hset A hA).symm) stronglyMeasurable_const.aestronglyMeasurable

/-- A future-supported deterministic-energy observation under the actual
Girsanov measure is Gaussian and independent of the ENTIRE original past. -/
theorem law_and_independent (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u v : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (hvs : ∀ᵐ p ∂νin, p.1 ≤ s → v p = 0)
    (q : ℝ≥0) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ (q : ℝ)) :
    HasLaw (shift P e u v) (gaussianReal 0 q) (measure P e u) ∧
      Indep (MeasurableSpace.comap (shift P e u v) (borel ℝ)) (F s) (measure P e u) := by
  letI : IsProbabilityMeasure (measure P e u) := probability P e u K hK hu
  have hG (a : ℝ) : (∫ z : ℝ, Real.exp (a * z) ∂gaussianReal 0 q) = Real.exp (a ^ 2 * (q : ℝ) / 2) := by
    change ProbabilityTheory.mgf id (gaussianReal 0 q) a = _
    rw [mgf_id_gaussianReal]
    simp [mul_comm]
  apply ConditionalMGF.law_and_independent (F s) (F.le s)
    (shift_stronglyMeasurable P e u v).measurable
    (fun a ↦ integrable_exp_mul_gaussianReal a)
    (fun a ↦ (NativeGirsanovTilt.mgf P e u v K hK hu q q.coe_nonneg hv a).1)
  intro a
  simpa only [hG] using conditional_mgf P e s hsH u v K hK hu hvs q q.coe_nonneg hv a

theorem restricted_law (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u v : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (hvs : ∀ᵐ p ∂νin, p.1 ≤ s → v p = 0)
    (q : ℝ≥0) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ (q : ℝ))
    (A : Set Ω) (hA : MeasurableSet[F s] A) :
    ((measure P e u).restrict A).map (shift P e u v) = (measure P e u) A • gaussianReal 0 q := by
  letI : IsProbabilityMeasure (measure P e u) := probability P e u K hK hu
  have hG (a : ℝ) : (∫ z : ℝ, Real.exp (a * z) ∂gaussianReal 0 q) = Real.exp (a ^ 2 * (q : ℝ) / 2) := by
    change ProbabilityTheory.mgf id (gaussianReal 0 q) a = _
    rw [mgf_id_gaussianReal]
    simp [mul_comm]
  exact ConditionalMGF.restricted_law (F s) (F.le s)
    (shift_stronglyMeasurable P e u v).measurable
    (fun a ↦ integrable_exp_mul_gaussianReal a)
    (fun a ↦ (NativeGirsanovTilt.mgf P e u v K hK hu q q.coe_nonneg hv a).1)
    (fun a ↦ by simpa only [hG] using conditional_mgf P e s hsH u v K hK hu hvs q q.coe_nonneg hv a) hA

theorem characteristic_on_event (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u v : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (hvs : ∀ᵐ p ∂νin, p.1 ≤ s → v p = 0)
    (q : ℝ≥0) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ (q : ℝ))
    (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ ω in A, Complex.exp ((shift P e u v ω : ℂ) * Complex.I) ∂measure P e u) =
      (measure P e u).real A • (Real.exp (-(q : ℝ) / 2) : ℂ) := by
  have hZ := (shift_stronglyMeasurable P e u v).measurable
  have hres := restricted_law P e s hsH u v K hK hu hvs q hv A hA
  have hchar : (∫ z : ℝ, Complex.exp ((z : ℂ) * Complex.I) ∂gaussianReal 0 q) =
      (Real.exp (-(q : ℝ) / 2) : ℂ) := by
    calc
      _ = charFun (gaussianReal 0 q) (1 : ℝ) := by
        rw [charFun_apply]
        simp only [Real.inner_apply, mul_one]
      _ = _ := by
        rw [charFun_gaussianReal, Complex.ofReal_exp]
        simp only [Complex.ofReal_zero, Complex.ofReal_one, one_mul, one_pow, mul_zero,
          zero_mul, zero_sub, mul_one, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
        rw [neg_div]
  calc
    _ = ∫ z : ℝ, Complex.exp ((z : ℂ) * Complex.I)
        ∂((measure P e u).restrict A).map (shift P e u v) :=
      (integral_map hZ.aemeasurable.restrict (by fun_prop)).symm
    _ = _ := by rw [hres, integral_smul_measure, hchar]; rfl

end SHEStochastic.NativeGirsanovFullPast
