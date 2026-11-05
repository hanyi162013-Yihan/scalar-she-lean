module

public import SHEStochastic.BrownianGaussianStep
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GaussianCharacteristicDefect
open MeasureTheory ProbabilityTheory

/-- Gaussian damping is one-half Lipschitz as a function of a
nonnegative variance. The constant is independent of the variance. -/
theorem damping_lipschitz {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-y / 2) - Real.exp (-x / 2)| ≤ (1 / 2 : ℝ) * |y - x| := by
  have hd (z : ℝ) : HasDerivAt (fun z : ℝ ↦ Real.exp (-z / 2))
      (Real.exp (-z / 2) * (-1 / 2)) z := by
    simpa using (((hasDerivAt_id z).neg.div_const 2).exp)
  have hb (z : ℝ) (hz : z ∈ Set.Ici (0 : ℝ)) :
      ‖Real.exp (-z / 2) * (-1 / 2)‖ ≤ (1 / 2 : ℝ) := by
    have hz0 : 0 ≤ z := hz
    have he : Real.exp (-z / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    norm_num
    linarith
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ ↦ (hd z).hasDerivWithinAt) hb hx hy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded past-measurable weight may be retained in the Gaussian
step estimate. This includes indicators of every event in the full past. -/
theorem weighted_step_defect (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[m] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1)
    {D V : Ω → ℝ} (hD : @Measurable Ω ℝ mΩ _ D)
    (hV : letI : MeasurableSpace Ω := mΩ; Integrable V μ)
    (hV0 : ∀ ω, 0 ≤ V ω) {q : ℝ} (hq : 0 ≤ q)
    (hc : letI : MeasurableSpace Ω := mΩ
      μ[fun ω ↦ Complex.exp ((D ω : ℂ) * Complex.I) | m] =ᵐ[μ]
        (fun ω ↦ (Real.exp (-V ω / 2) : ℂ))) :
    letI : MeasurableSpace Ω := mΩ
    ‖(∫ ω, φ ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      (Real.exp (-q / 2) : ℂ) * (∫ ω, φ ω ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∫ ω, |V ω - q| ∂μ := by
  letI : MeasurableSpace Ω := mΩ
  let f : Ω → ℂ := fun ω ↦ Complex.exp ((D ω : ℂ) * Complex.I)
  let g : Ω → ℂ := fun ω ↦ (Real.exp (-V ω / 2) : ℂ)
  let c : ℂ := Real.exp (-q / 2)
  have hφi : Integrable φ μ := Integrable.of_bound (hφ.mono hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall hφbound)
  have hfi : Integrable f μ := Integrable.of_bound (by dsimp [f]; fun_prop) 1
    (Filter.Eventually.of_forall fun ω ↦ by simp [f])
  have hφfi : Integrable (fun ω ↦ φ ω * f ω) μ := Integrable.of_bound
    ((hφ.mono hm).aestronglyMeasurable.mul hfi.aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun ω ↦ by simpa [f, norm_mul] using hφbound ω)
  have hp := condExp_bilin_of_stronglyMeasurable_left
    (ContinuousLinearMap.mul ℝ ℂ) hφ hφfi hfi
  have hpg : μ[fun ω ↦ φ ω * f ω | m] =ᵐ[μ] (fun ω ↦ φ ω * g ω) := by
    filter_upwards [hp, hc] with ω hω hωc
    exact hω.trans (congrArg (fun z : ℂ ↦ φ ω * z) hωc)
  have hφgi : Integrable (fun ω ↦ φ ω * g ω) μ := integrable_condExp.congr hpg
  have he : (∫ ω, φ ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) =
      ∫ ω, φ ω * g ω ∂μ := by
    change (∫ ω, φ ω * f ω ∂μ) = _
    rw [← integral_condExp hm]
    exact integral_congr_ae hpg
  rw [he]
  change ‖(∫ ω, φ ω * g ω ∂μ) - c * ∫ ω, φ ω ∂μ‖ ≤ _
  rw [← integral_const_mul, ← integral_sub hφgi (hφi.const_mul c)]
  have hb : ∀ ω, ‖φ ω * g ω - c * φ ω‖ ≤ (1 / 2 : ℝ) * |V ω - q| := by
    intro ω
    rw [mul_comm c, ← mul_sub, norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hφbound ω)).trans
    have hgc : g ω - c = ((Real.exp (-V ω / 2) - Real.exp (-q / 2) : ℝ) : ℂ) := by
      simp [g, c]
    rw [hgc, Complex.norm_real, Real.norm_eq_abs]
    exact damping_lipschitz hq (hV0 ω)
  calc
    _ ≤ ∫ ω, (1 / 2 : ℝ) * |V ω - q| ∂μ :=
      norm_integral_le_of_norm_le (((hV.sub (integrable_const q)).abs).const_mul (1 / 2))
        (Filter.Eventually.of_forall hb)
    _ = _ := integral_const_mul _ _

/-- A conditional Gaussian step contributes at most half its mean
variance error to the characteristic-function error. No bound on the
random frequency or on the variance is needed. -/
theorem step_defect (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {S D V : Ω → ℝ} (hS : Measurable[m] S) (hD : @Measurable Ω ℝ mΩ _ D)
    (hV : letI : MeasurableSpace Ω := mΩ; Integrable V μ)
    (hV0 : ∀ ω, 0 ≤ V ω) {q : ℝ} (hq : 0 ≤ q)
    (hc : letI : MeasurableSpace Ω := mΩ
      μ[fun ω ↦ Complex.exp ((D ω : ℂ) * Complex.I) | m] =ᵐ[μ]
        (fun ω ↦ (Real.exp (-V ω / 2) : ℂ))) :
    letI : MeasurableSpace Ω := mΩ
    ‖(∫ ω, Complex.exp (((S ω + D ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      (Real.exp (-q / 2) : ℂ) * (∫ ω, Complex.exp ((S ω : ℂ) * Complex.I) ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∫ ω, |V ω - q| ∂μ := by
  letI : MeasurableSpace Ω := mΩ
  have hφ : StronglyMeasurable[m] (fun ω ↦ Complex.exp ((S ω : ℂ) * Complex.I)) := by fun_prop
  simpa only [Complex.ofReal_add, add_mul, Complex.exp_add] using
    weighted_step_defect m hm _ hφ (fun ω ↦ by simp) hD hV hV0 hq hc

/-- Errors in a sequence of contractions accumulate additively. -/
theorem telescoping_defect_from_initial (z d : ℕ → ℂ) (e : ℕ → ℝ)
    (hd : ∀ k, ‖d k‖ ≤ 1) (he : ∀ k, ‖z (k + 1) - d k * z k‖ ≤ e k) (N : ℕ) :
    ‖z N - (∏ k ∈ Finset.range N, d k) * z 0‖ ≤ ∑ k ∈ Finset.range N, e k := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    calc
      _ = ‖(z (N + 1) - d N * z N) + d N * (z N - (∏ k ∈ Finset.range N, d k) * z 0)‖ := by
        congr 1
        ring
      _ ≤ ‖z (N + 1) - d N * z N‖ + ‖d N * (z N - (∏ k ∈ Finset.range N, d k) * z 0)‖ :=
        norm_add_le _ _
      _ ≤ e N + ∑ k ∈ Finset.range N, e k := by
        apply add_le_add (he N)
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hd N)).trans hN
      _ = _ := add_comm _ _

theorem telescoping_defect (z d : ℕ → ℂ) (e : ℕ → ℝ) (hz : z 0 = 1)
    (hd : ∀ k, ‖d k‖ ≤ 1) (he : ∀ k, ‖z (k + 1) - d k * z k‖ ≤ e k) (N : ℕ) :
    ‖z N - ∏ k ∈ Finset.range N, d k‖ ≤ ∑ k ∈ Finset.range N, e k := by
  simpa only [hz, mul_one] using telescoping_defect_from_initial z d e hd he N

/-- Quantitative finite-grid Gaussian recognition. If each increment
has a conditional Gaussian characteristic function, replacing its random
variance by deterministic variances costs only their total L1 error. -/
theorem weighted_finite_steps_defect (F : Filtration ℕ mΩ)
    (φ : Ω → ℂ) (hφ : StronglyMeasurable[F 0] φ) (hφbound : ∀ ω, ‖φ ω‖ ≤ 1)
    (M : ℕ → Ω → ℝ)
    (hM : StronglyAdapted F M) (hM0 : M 0 =ᵐ[μ] fun _ ↦ 0)
    (V : ℕ → Ω → ℝ) (hV : ∀ k, Integrable (V k) μ) (hV0 : ∀ k ω, 0 ≤ V k ω)
    (q : ℕ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hc : ∀ k, μ[fun ω ↦ Complex.exp (((M (k + 1) ω - M k ω : ℝ) : ℂ) * Complex.I)
        | F k] =ᵐ[μ] (fun ω ↦ (Real.exp (-V k ω / 2) : ℂ))) (N : ℕ) :
    ‖(∫ ω, φ ω * Complex.exp ((M N ω : ℂ) * Complex.I) ∂μ) -
      (Real.exp (-(∑ k ∈ Finset.range N, q k) / 2) : ℂ) * (∫ ω, φ ω ∂μ)‖ ≤
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, ∫ ω, |V k ω - q k| ∂μ := by
  let z (k : ℕ) : ℂ := ∫ ω, φ ω * Complex.exp ((M k ω : ℂ) * Complex.I) ∂μ
  let d (k : ℕ) : ℂ := Real.exp (-q k / 2)
  let e (k : ℕ) : ℝ := (1 / 2 : ℝ) * ∫ ω, |V k ω - q k| ∂μ
  have hz : z 0 = ∫ ω, φ ω ∂μ := by
    exact integral_congr_ae (hM0.mono fun ω hω ↦ by simp [hω])
  have hd (k : ℕ) : ‖d k‖ ≤ 1 := by
    change ‖(Real.exp (-q k / 2) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith [hq k])
  have he (k : ℕ) : ‖z (k + 1) - d k * z k‖ ≤ e k := by
    have hD : Measurable (fun ω ↦ M (k + 1) ω - M k ω) :=
      ((hM (k + 1)).mono (F.le _)).measurable.sub ((hM k).mono (F.le _)).measurable
    have hψ : StronglyMeasurable[F k]
        (fun ω ↦ φ ω * Complex.exp ((M k ω : ℂ) * Complex.I)) :=
      (hφ.mono (F.mono (Nat.zero_le k))).mul (by
        letI : MeasurableSpace Ω := F k
        have hMk : StronglyMeasurable (M k) := hM k
        fun_prop)
    have hh := weighted_step_defect (F k) (F.le k) _ hψ
      (fun ω ↦ by simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using hφbound ω)
      hD (hV k) (hV0 k) (hq k) (hc k)
    have hi (ω : Ω) :
        (φ ω * Complex.exp ((M k ω : ℂ) * Complex.I)) *
          Complex.exp (((M (k + 1) ω - M k ω : ℝ) : ℂ) * Complex.I) =
        φ ω * Complex.exp ((M (k + 1) ω : ℂ) * Complex.I) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    dsimp only [z, d, e]
    simpa only [hi] using hh
  have hp (n : ℕ) : (∏ k ∈ Finset.range n, d k) =
      (Real.exp (-(∑ k ∈ Finset.range n, q k) / 2) : ℂ) := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.prod_range_succ, hn, Finset.sum_range_succ]
      change (Real.exp (-((∑ k ∈ Finset.range n, q k)) / 2) : ℂ) *
        (Real.exp (-q n / 2) : ℂ) = _
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
  have ht := telescoping_defect_from_initial z d e hd he N
  rw [hp, hz] at ht
  simpa only [z, e, ← Finset.mul_sum] using ht

/-- Quantitative finite-grid Gaussian recognition. If each increment
has a conditional Gaussian characteristic function, replacing its random
variance by deterministic variances costs only their total L1 error. -/
theorem finite_steps_defect (F : Filtration ℕ mΩ) (M : ℕ → Ω → ℝ)
    (hM : StronglyAdapted F M) (hM0 : M 0 =ᵐ[μ] fun _ ↦ 0)
    (V : ℕ → Ω → ℝ) (hV : ∀ k, Integrable (V k) μ) (hV0 : ∀ k ω, 0 ≤ V k ω)
    (q : ℕ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hc : ∀ k, μ[fun ω ↦ Complex.exp (((M (k + 1) ω - M k ω : ℝ) : ℂ) * Complex.I)
        | F k] =ᵐ[μ] (fun ω ↦ (Real.exp (-V k ω / 2) : ℂ))) (N : ℕ) :
    ‖(∫ ω, Complex.exp ((M N ω : ℂ) * Complex.I) ∂μ) -
      (Real.exp (-(∑ k ∈ Finset.range N, q k) / 2) : ℂ)‖ ≤
      (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, ∫ ω, |V k ω - q k| ∂μ := by
  simpa only [one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, mul_one] using
    weighted_finite_steps_defect F (fun _ ↦ 1) stronglyMeasurable_const
      (fun _ ↦ by simp) M hM hM0 V hV hV0 q hq hc N

end SHEStochastic.GaussianCharacteristicDefect
