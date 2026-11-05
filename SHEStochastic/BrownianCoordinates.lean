module

public import SHE.BrownianShiftedFiniteLaw
public import Mathlib.Probability.Independence.Integration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.BrownianCoordinates
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (W : ι → ℝ≥0 → Ω → ℝ)
  (hW : ∀ n (a : Fin n → ι), FiniteBrownianLawOn F μ H (fun i ↦ W (a i))
    (fun i j ↦ if a i = a j then 1 else 0))

private theorem projection_law {n : ℕ} {Z : Ω → WordRecursion.State n}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (hZ : HasLaw Z (multivariateGaussian (0 : WordRecursion.State n) A) μ) (j : Fin n) :
    HasLaw (fun ω ↦ Z ω j) (gaussianReal 0 (A j j).toNNReal) μ := by
  have hp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : WordRecursion.State n)) hA (i := j)
  have he : HasLaw (fun z : WordRecursion.State n ↦ z j)
      (gaussianReal 0 (A j j).toNNReal) (multivariateGaussian 0 A) :=
    ⟨hp.measurable.aemeasurable, by simpa using hp.map_eq⟩
  exact he.comp hZ

include hW

/-- Scalar marginal law extracted from the paper's finite-horizon
Brownian coordinate interface. No law beyond H is required. -/
theorem eval_law (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    HasLaw (W i t) (gaussianReal 0 t) μ := by
  let a : Fin 1 → ι := fun _ ↦ i
  let u : Fin 1 → ℝ≥0 := fun _ ↦ t
  have hl := (hW 1 a).1 u (fun _ ↦ ht)
  have hp := projection_law μ (BrownianFiniteCovariance.posSemidef a u) hl 0
  simpa [BrownianFiniteCovariance.matrix, a, u] using hp

/-- Actual increment laws on the supplied finite interval. -/
theorem increment_law (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H) :
    HasLaw (fun ω ↦ W i t ω - W i s ω) (gaussianReal 0 (t - s)) μ := by
  let a : Fin 1 → ι := fun _ ↦ i
  let u : Fin 1 → ℝ≥0 := fun _ ↦ t - s
  have hstH : s + (t - s) ≤ H := by simpa only [add_tsub_cancel_of_le hst] using ht
  have hl := BrownianShiftedFiniteLaw.law F μ H W hW s (t - s) hstH a u (fun _ ↦ le_rfl)
  have hp := projection_law μ (BrownianFiniteCovariance.posSemidef a u) hl 0
  simpa [BrownianFiniteCovariance.matrix, a, u, add_tsub_cancel_of_le hst] using hp

theorem memLp_eval (i : ι) (t : ℝ≥0) (ht : t ≤ H) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (W i t) p μ :=
  (eval_law F μ H W hW i t ht).memLp (memLp_id_gaussianReal' p hp)

theorem memLp_increment (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω ↦ W i t ω - W i s ω) p μ :=
  (increment_law F μ H W hW i s t hst ht).memLp (memLp_id_gaussianReal' p hp)

theorem integral_increment (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H) :
    ∫ ω, W i t ω - W i s ω ∂μ = 0 := by
  have he := (increment_law F μ H W hW i s t hst ht).integral_eq
  rwa [integral_id_gaussianReal] at he

/-- Each future coordinate increment is independent of the FULL
supplied past sigma algebra, directly from the recognized vector law. -/
theorem independent_increment (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H) :
    Indep (MeasurableSpace.comap (fun ω ↦ W i t ω - W i s ω) inferInstance) (F s) μ := by
  let a : Fin 1 → ι := fun _ ↦ i
  let V (ω : Ω) : WordRecursion.State 1 := WithLp.toLp 2 (fun _ ↦ W i t ω - W i s ω)
  have hind : Indep (MeasurableSpace.comap V inferInstance) (F s) μ := (hW 1 a).2 s t hst ht
  apply indep_of_indep_of_le_left hind
  have he : (fun ω ↦ W i t ω - W i s ω) =
      (fun z : WordRecursion.State 1 ↦ z 0) ∘ V := rfl
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (Measurable.comap_le ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).measurable))

theorem adapted_indepFun_increment (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) :
    IndepFun φ (fun ω ↦ W i t ω - W i s ω) μ := by
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact indep_of_indep_of_le_left (independent_increment F μ H W hW i s t hst ht).symm
    (Measurable.comap_le hφ)

theorem integral_adapted_mul_increment (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) :
    ∫ ω, φ ω * (W i t ω - W i s ω) ∂μ = 0 := by
  have hi := adapted_indepFun_increment F μ H W hW i s t hst ht hφ
  have hm : Measurable φ := hφ.mono (F.le s) le_rfl
  rw [hi.integral_fun_mul_eq_mul_integral hm.aestronglyMeasurable
    (memLp_increment F μ H W hW i s t hst ht 2 (by simp)).aestronglyMeasurable,
    integral_increment F μ H W hW i s t hst ht, mul_zero]

theorem memLp_adapted_mul_increment (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) (hφL2 : MemLp φ 2 μ) :
    MemLp (fun ω ↦ φ ω * (W i t ω - W i s ω)) 2 μ := by
  have hi := (adapted_indepFun_increment F μ H W hW i s t hst ht hφ).comp
    (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2) (by fun_prop) (by fun_prop)
  have hΔ := memLp_increment F μ H W hW i s t hst ht 2 (by simp)
  have hp : Integrable (fun ω ↦ φ ω ^ 2 * (W i t ω - W i s ω) ^ 2) μ :=
    hi.integrable_mul hφL2.integrable_sq hΔ.integrable_sq
  have hm : Measurable φ := hφ.mono (F.le s) le_rfl
  have hmeas : AEStronglyMeasurable (fun ω ↦ φ ω * (W i t ω - W i s ω)) μ :=
    hm.aestronglyMeasurable.mul hΔ.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).mpr (by simpa only [mul_pow] using hp)

/-- Conditional covariance at a common right endpoint. The coefficient
is measurable in the full past; orthogonality of distinct noise coordinates
comes from the actual finite-dimensional Gaussian law. -/
theorem weighted_common_increment (i j : ι) (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H)
    {φ : Ω → ℝ} (hφ : Measurable[F s] φ) :
    (∫ ω, φ ω * ((W i t ω - W i s ω) * (W j t ω - W j s ω)) ∂μ) =
      (∫ ω, φ ω ∂μ) * (((t : ℝ) - s) * (if i = j then 1 else 0)) := by
  let a : Fin 2 → ι := ![i, j]
  let u : Fin 2 → ℝ≥0 := fun _ ↦ t - s
  let D (ω : Ω) : WordRecursion.State 2 :=
    WithLp.toLp 2 (fun k ↦ W (a k) t ω - W (a k) s ω)
  let A := BrownianFiniteCovariance.matrix a u
  have hA : A.PosSemidef := BrownianFiniteCovariance.posSemidef a u
  have hstH : s + (t - s) ≤ H := by simpa only [add_tsub_cancel_of_le hst] using ht
  have hLaw : HasLaw D (multivariateGaussian (0 : WordRecursion.State 2) A) μ := by
    simpa only [D, A, u, add_tsub_cancel_of_le hst] using
      BrownianShiftedFiniteLaw.law F μ H W hW s (t - s) hstH a u (fun _ ↦ le_rfl)
  have hiV : IndepFun φ D μ := by
    apply (IndepFun_iff_Indep _ _ _).mpr
    exact indep_of_indep_of_le_left ((hW 2 a).2 s t hst ht).symm (Measurable.comap_le hφ)
  have hprodMeas : Measurable (fun z : WordRecursion.State 2 ↦ z 0 * z 1) := by fun_prop
  have hi := hiV.comp (φ := (id : ℝ → ℝ))
    (ψ := fun z : WordRecursion.State 2 ↦ z 0 * z 1) measurable_id hprodMeas
  have hm : Measurable φ := hφ.mono (F.le s) le_rfl
  have hp : AEStronglyMeasurable (fun ω ↦ D ω 0 * D ω 1) μ :=
    (hprodMeas.comp_aemeasurable hLaw.aemeasurable).aestronglyMeasurable
  have he := hi.integral_fun_mul_eq_mul_integral hm.aestronglyMeasurable hp
  simp only [Function.comp_apply, id_eq] at he
  have hmoment : (∫ ω, D ω 0 * D ω 1 ∂μ) =
      ((t : ℝ) - s) * (if i = j then 1 else 0) := by
    calc
      _ = ∫ z : WordRecursion.State 2, z 0 * z 1 ∂multivariateGaussian 0 A :=
        hLaw.integral_comp hprodMeas.aestronglyMeasurable
      _ = A 0 1 := GaussianIncrement.coordinate_product_moment hA 0 1
      _ = _ := by simp [A, BrownianFiniteCovariance.matrix, a, u, NNReal.coe_sub hst]
  change (∫ ω, φ ω * (D ω 0 * D ω 1) ∂μ) = _
  rw [he, hmoment]

end SHEStochastic.BrownianCoordinates
