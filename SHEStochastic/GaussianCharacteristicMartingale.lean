module

public import SHEStochastic.BrownianGaussianStep
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GaussianCharacteristicMartingale
open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A conditional characteristic function gives the compensated
exponential identity by the ordinary pull-out property. -/
theorem conditional_step (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Measurable[m] X)
    (hY : @Measurable Ω ℝ mΩ _ Y) (S T : ℝ)
    (hCE : μ[fun ω ↦ Complex.exp ((Y ω-X ω : ℝ) * Complex.I) | m] =ᵐ[μ]
      fun _ ↦ Complex.exp (-(T-S : ℝ))) :
    μ[fun ω ↦ Complex.exp ((Y ω : ℂ) * Complex.I + (T : ℂ)) | m] =ᵐ[μ]
      fun ω ↦ Complex.exp ((X ω : ℂ) * Complex.I + (S : ℂ)) := by
  let f := fun ω ↦ Complex.exp ((X ω : ℂ) * Complex.I + (T : ℂ))
  let g := fun ω ↦ Complex.exp ((Y ω-X ω : ℝ) * Complex.I)
  have hf : StronglyMeasurable[m] f := by fun_prop
  have hg : @Measurable Ω ℂ mΩ _ g := by
    apply Complex.continuous_exp.measurable.comp
    exact (Complex.continuous_ofReal.measurable.comp (hY.sub (hX.mono hm le_rfl))).mul measurable_const
  have hig : Integrable g μ := (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by simp [g, Complex.norm_exp])
  have hip : Integrable (fun ω ↦ f ω * g ω) μ := by
    apply (integrable_const (Real.exp T)).mono'
      ((hf.measurable.mono hm le_rfl).mul hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω ↦ by simp [f, g, norm_mul, Complex.norm_exp]
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf hip hig
  change μ[fun ω ↦ f ω * g ω | m] =ᵐ[μ] fun ω ↦ f ω * μ[g | m] ω at hp
  have he (ω : Ω) : Complex.exp ((Y ω : ℂ) * Complex.I + (T : ℂ)) = f ω * g ω := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  apply (condExp_congr_ae (Filter.Eventually.of_forall he)).trans
  filter_upwards [hp, hCE] with ω hp hω
  rw [hp, hω]
  change Complex.exp _ * Complex.exp _ = Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite-horizon characteristic exponential is a genuine
martingale in the supplied full filtration. Its modulus is deterministic,
so no exponential moment or Novikov hypothesis enters. -/
theorem conditional_increment (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X Y : Ω → ℝ) (hX : Measurable[m] X)
    (hY : @Measurable Ω ℝ mΩ _ Y) (S T : ℝ)
    (hCE : μ[fun ω ↦ Complex.exp ((Y ω : ℂ)*Complex.I+(T : ℂ)) | m] =ᵐ[μ]
      fun ω ↦ Complex.exp ((X ω : ℂ)*Complex.I+(S : ℂ))) :
    μ[fun ω ↦ Complex.exp ((Y ω-X ω : ℝ)*Complex.I) | m] =ᵐ[μ]
      fun _ ↦ Complex.exp (-(T-S : ℝ)) := by
  let f := fun ω ↦ Complex.exp (-(X ω : ℂ)*Complex.I-(T : ℂ))
  let g := fun ω ↦ Complex.exp ((Y ω : ℂ)*Complex.I+(T : ℂ))
  have hf : StronglyMeasurable[m] f := by fun_prop
  have hg : @Measurable Ω ℂ mΩ _ g := by fun_prop
  have hig : Integrable g μ := (integrable_const (Real.exp T)).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by simp [g, Complex.norm_exp])
  have hip : Integrable (fun ω ↦ f ω*g ω) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hf.measurable.mono hm le_rfl).mul hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω ↦ by
      change ‖Complex.exp (-(X ω : ℂ)*Complex.I-(T : ℂ)) *
        Complex.exp ((Y ω : ℂ)*Complex.I+(T : ℂ))‖ ≤ 1
      rw [← Complex.exp_add, Complex.norm_exp]
      simp
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf hip hig
  change μ[fun ω ↦ f ω*g ω | m] =ᵐ[μ] fun ω ↦ f ω*μ[g | m] ω at hp
  have he (ω : Ω) : Complex.exp ((Y ω-X ω : ℝ)*Complex.I) = f ω*g ω := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  apply (condExp_congr_ae (Filter.Eventually.of_forall he)).trans
  filter_upwards [hp, hCE] with ω hp hω
  rw [hp, hω]
  change Complex.exp _*Complex.exp _ = Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite-horizon characteristic exponential is a genuine
martingale in the supplied full filtration. Its modulus is deterministic,
so no exponential moment or Novikov hypothesis enters. -/
theorem martingale (F : Filtration ℝ≥0 mΩ) (H : ℝ≥0)
    (Z : ℝ≥0 → Ω → ℝ) (hZ : ∀ t, Measurable[F t] (Z t)) (c : ℝ)
    (hCE : ∀ s t : ℝ≥0, s ≤ t → t ≤ H →
      μ[fun ω ↦ Complex.exp ((Z t ω-Z s ω : ℝ) * Complex.I) | F s] =ᵐ[μ]
        fun _ ↦ Complex.exp (-(c * ((t : ℝ)-(s : ℝ)) : ℝ))) :
    Martingale (fun t ω ↦ Complex.exp ((Z (min t H) ω : ℂ) * Complex.I +
      (c * (min t H : ℝ≥0) : ℝ))) F μ := by
  have ha (t : ℝ≥0) : StronglyMeasurable[F t] (fun ω ↦
      Complex.exp ((Z (min t H) ω : ℂ) * Complex.I + (c * (min t H : ℝ≥0) : ℝ))) := by
    have hz := (hZ (min t H)).mono (F.mono (min_le_left _ _)) le_rfl
    fun_prop
  refine ⟨ha, fun s t hst ↦ ?_⟩
  by_cases hs : s ≤ H
  · have hsq : s ≤ min t H := le_min hst hs
    have hh := conditional_step μ (F s) (F.le s) (Z s) (Z (min t H))
      (hZ s) ((hZ _).mono (F.le _) le_rfl) (c*s) (c*(min t H : ℝ≥0)) ?_
    · simpa only [min_eq_left hs] using hh
    · convert hCE s (min t H) hsq (min_le_right _ _) using 1
      congr 1
      funext ω
      congr 1
      push_cast
      ring
  · have hHs := (le_of_not_ge hs)
    have hHt := hHs.trans hst
    simp only [min_eq_right hHs, min_eq_right hHt]
    apply Filter.EventuallyEq.of_eq
    apply condExp_of_stronglyMeasurable (F.le s)
    · simpa only [min_eq_right hHs] using ha s
    · apply (integrable_const (Real.exp (c*H))).mono'
        (by simpa only [min_eq_right hHs] using (ha s).mono (F.le s) |>.aestronglyMeasurable)
      exact Filter.Eventually.of_forall fun ω ↦ by simp [Complex.norm_exp]

section FiniteFamily
open SHE Matrix
open scoped InnerProductSpace
variable {ι : Type*} [DecidableEq ι]
  {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0}

theorem covariance_scale {n : ℕ} (a : Fin n → ι) (d : ℝ≥0) (r : WordRecursion.State n) :
    r ⬝ᵥ BrownianFiniteCovariance.matrix a (fun _ ↦ d) *ᵥ r =
      (d : ℝ) * (r ⬝ᵥ BrownianFiniteCovariance.matrix a (fun _ ↦ 1) *ᵥ r) := by
  simp [BrownianFiniteCovariance.matrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

def variance {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) : ℝ :=
  (r ⬝ᵥ BrownianFiniteCovariance.matrix a (fun _ ↦ 1) *ᵥ r) / 2

theorem variance_nonneg {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) :
    0 ≤ variance a r := by
  change 0 ≤ (r ⬝ᵥ BrownianFiniteCovariance.matrix a (fun _ ↦ 1) *ᵥ r) / 2
  apply div_nonneg _ (by norm_num)
  simpa only [star_trivial] using
    (BrownianFiniteCovariance.posSemidef a (fun _ ↦ 1)).dotProduct_mulVec_nonneg r

def phase (P : FiniteScalarIto.Family F μ H ι) {n : ℕ} (a : Fin n → ι)
    (r : WordRecursion.State n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  inner ℝ (WithLp.toLp 2 (fun i ↦ P.W (a i) t ω)) r

/-- Every finite linear combination of the actual Brownian coordinates
has the characteristic martingale in the full supplied filtration.
Repeated coordinates are retained with their exact covariance. -/
theorem family (P : FiniteScalarIto.Family F μ H ι) {n : ℕ} (a : Fin n → ι)
    (r : WordRecursion.State n) :
    Martingale (fun t ω ↦ Complex.exp ((phase μ P a r (min t H) ω : ℂ) * Complex.I +
      (variance a r * (min t H : ℝ≥0) : ℝ))) F μ := by
  have hm (t : ℝ≥0) : Measurable[F t] (phase μ P a r t) := by
    have hw (i : Fin n) : Measurable[F t] (P.W (a i) t) := P.adapted (a i) t
    letI : MeasurableSpace Ω := F t
    exact ((WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (measurable_pi_iff.mpr hw)).inner measurable_const
  apply martingale μ F H (phase μ P a r) hm (variance a r)
  intro s t hst htH
  have hh := FiniteScalarIto.condExp_gaussian_step P a s t hst htH
    (R := fun _ ↦ r) measurable_const
  have he (ω : Ω) : phase μ P a r t ω - phase μ P a r s ω =
      inner ℝ (WithLp.toLp 2 (fun i ↦ P.W (a i) t ω-P.W (a i) s ω)) r := by
    rw [phase, phase, ← inner_sub_left]
    rfl
  simp_rw [he]
  apply hh.trans
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [covariance_scale]
    congr 1
    dsimp only [variance]
    rw [NNReal.coe_sub hst]
    push_cast
    ring

/-- Centering by the initial driver value is exact and does not require
choosing a common zero-start event for randomly stopped times. -/
theorem family_centered (P : FiniteScalarIto.Family F μ H ι) {n : ℕ} (a : Fin n → ι)
    (r : WordRecursion.State n) :
    Martingale (fun t ω ↦ Complex.exp
      (((phase μ P a r (min t H) ω-phase μ P a r 0 ω : ℝ) : ℂ) * Complex.I +
        (variance a r * (min t H : ℝ≥0) : ℝ))) F μ := by
  have hm (t : ℝ≥0) : Measurable[F t] (phase μ P a r t) := by
    have hw (i : Fin n) : Measurable[F t] (P.W (a i) t) := P.adapted (a i) t
    letI : MeasurableSpace Ω := F t
    exact ((WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (measurable_pi_iff.mpr hw)).inner measurable_const
  apply martingale μ F H (fun t ω ↦ phase μ P a r t ω-phase μ P a r 0 ω)
    (fun t ↦ (hm t).sub ((hm 0).mono (F.mono bot_le) le_rfl)) (variance a r)
  intro s t hst htH
  have he (ω : Ω) : (phase μ P a r t ω-phase μ P a r 0 ω) -
      (phase μ P a r s ω-phase μ P a r 0 ω) =
        inner ℝ (WithLp.toLp 2 (fun i ↦ P.W (a i) t ω-P.W (a i) s ω)) r := by
    rw [sub_sub_sub_cancel_right, phase, phase, ← inner_sub_left]
    rfl
  simp_rw [he]
  apply (FiniteScalarIto.condExp_gaussian_step P a s t hst htH
    (R := fun _ ↦ r) measurable_const).trans
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [covariance_scale]
    congr 1
    dsimp only [variance]
    rw [NNReal.coe_sub hst]
    push_cast
    ring

end FiniteFamily
end SHEStochastic.GaussianCharacteristicMartingale
