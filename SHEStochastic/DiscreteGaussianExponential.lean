module

public import SHEStochastic.ConditionalGaussianMGF
public import Mathlib.Probability.Martingale.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.DiscreteGaussianExponential
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The cell identities used below. A native Hilbert simple process
will supply all fields; this record introduces no accepted axiom. -/
structure Model (F : Filtration ℕ mΩ) (μ : Measure Ω) where
  increment : ℕ → Ω → ℝ
  variance : ℕ → Ω → ℝ
  increment_adapted : ∀ k, StronglyMeasurable[F (k + 1)] (increment k)
  variance_adapted : ∀ k, StronglyMeasurable[F k] (variance k)
  variance_nonneg : ∀ k ω, 0 ≤ variance k ω
  exp_integrable : ∀ k a, Integrable (fun ω ↦ Real.exp (a * increment k ω)) μ
  normalized : ∀ k a, μ[fun ω ↦ Real.exp
    (a * increment k ω - a ^ 2 * variance k ω / 2) | F k] =ᵐ[μ] fun _ ↦ 1

namespace Model
variable {F : Filtration ℕ mΩ} (M : Model F μ)

def sumIncrement (N : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range N, M.increment k ω
def sumVariance (N : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range N, M.variance k ω
def exponential (a : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  Real.exp (a * M.sumIncrement N ω - a ^ 2 * M.sumVariance N ω / 2)

theorem sumIncrement_adapted (N : ℕ) : StronglyMeasurable[F N] (M.sumIncrement N) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  apply (M.increment_adapted k).mono (F.mono _)
  have h := Finset.mem_range.mp hk
  omega

theorem sumVariance_adapted (N : ℕ) : StronglyMeasurable[F N] (M.sumVariance N) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  exact (M.variance_adapted k).mono (F.mono (Finset.mem_range.mp hk).le)

theorem sumVariance_nonneg (N : ℕ) (ω : Ω) : 0 ≤ M.sumVariance N ω :=
  Finset.sum_nonneg (fun k _ ↦ M.variance_nonneg k ω)

omit M in
theorem memLp_exp_two (Y : Ω → ℝ) (hY : StronglyMeasurable Y) (a : ℝ)
    (hi : Integrable (fun ω ↦ Real.exp ((2 * a) * Y ω)) μ) :
    MemLp (fun ω ↦ Real.exp (a * Y ω)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have he : (fun ω ↦ Real.exp (a * Y ω) ^ 2) =
      (fun ω ↦ Real.exp ((2 * a) * Y ω)) := by
    funext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rwa [he]

/-- Finite sums have exponential moments of every real order. This
uses only the already proved cell exponential moments and Holder. -/
theorem exp_sum_integrable (N : ℕ) (a : ℝ) :
    Integrable (fun ω ↦ Real.exp (a * M.sumIncrement N ω)) μ := by
  induction N generalizing a with
  | zero => simpa [sumIncrement] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω ↦ 1) μ)
  | succ N ih =>
    have hM := memLp_exp_two (M.sumIncrement N)
      ((M.sumIncrement_adapted N).mono (F.le N)) a (ih (2 * a))
    have hD := memLp_exp_two (M.increment N)
      ((M.increment_adapted N).mono (F.le (N + 1))) a (M.exp_integrable N (2 * a))
    convert hM.integrable_mul hD using 1
    funext ω
    simp only [sumIncrement, Finset.sum_range_succ, mul_add, Real.exp_add, Pi.mul_apply]

theorem exponential_adapted (a : ℝ) (N : ℕ) : StronglyMeasurable[F N] (M.exponential a N) := by
  have hS := M.sumIncrement_adapted N
  have hV := M.sumVariance_adapted N
  change StronglyMeasurable[F N] (fun ω ↦ Real.exp
    (a * M.sumIncrement N ω - a ^ 2 * M.sumVariance N ω / 2))
  exact (show Continuous (fun p : ℝ × ℝ ↦ Real.exp (a * p.1 - a ^ 2 * p.2 / 2)) from by
    fun_prop).comp_stronglyMeasurable (hS.prodMk hV)

theorem exponential_integrable (a : ℝ) (N : ℕ) : Integrable (M.exponential a N) μ := by
  apply (M.exp_sum_integrable N a).mono' ((M.exponential_adapted a N).mono (F.le N)).aestronglyMeasurable
  filter_upwards with ω
  change ‖Real.exp (a * M.sumIncrement N ω - a ^ 2 * M.sumVariance N ω / 2)‖ ≤ _
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (div_nonneg (mul_nonneg (sq_nonneg _) (M.sumVariance_nonneg N ω)) (by norm_num))

theorem exponential_succ (a : ℝ) (N : ℕ) (ω : Ω) :
    M.exponential a (N + 1) ω = M.exponential a N ω *
      Real.exp (a * M.increment N ω - a ^ 2 * M.variance N ω / 2) := by
  simp only [exponential, sumIncrement, sumVariance, Finset.sum_range_succ]
  rw [← Real.exp_add]
  congr 1
  ring

theorem conditional_succ (a : ℝ) (N : ℕ) :
    μ[M.exponential a (N + 1) | F N] =ᵐ[μ] M.exponential a N := by
  let f (ω : Ω) := Real.exp (a * M.increment N ω - a ^ 2 * M.variance N ω / 2)
  have hf : Integrable f μ := by
    apply (M.exp_integrable N a).mono' (by
      have hD := (M.increment_adapted N).mono (F.le (N + 1))
      have hV := (M.variance_adapted N).mono (F.le N)
      dsimp [f]
      fun_prop)
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact sub_le_self _ (div_nonneg (mul_nonneg (sq_nonneg _) (M.variance_nonneg N ω)) (by norm_num))
  have he : M.exponential a (N + 1) = (fun ω ↦ M.exponential a N ω * f ω) :=
    funext (M.exponential_succ a N)
  have hprod : Integrable (fun ω ↦ M.exponential a N ω * f ω) μ := by
    rw [← he]
    exact M.exponential_integrable a (N + 1)
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ)
    (M.exponential_adapted a N) hprod hf
  change μ[fun ω ↦ M.exponential a N ω * f ω | F N] =ᵐ[μ]
    (fun ω ↦ M.exponential a N ω * μ[f | F N] ω) at hp
  rw [he]
  filter_upwards [hp, M.normalized N a] with ω hω hc
  rw [hω]
  change M.exponential a N ω * μ[fun ω ↦ Real.exp
    (a * M.increment N ω - a ^ 2 * M.variance N ω / 2) | F N] ω = _
  rw [hc, mul_one]

theorem martingale (a : ℝ) : Martingale (M.exponential a) F μ :=
  martingale_nat (M.exponential_adapted a) (M.exponential_integrable a)
    (fun N ↦ (M.conditional_succ a N).symm)

theorem integral_eq_one (a : ℝ) (N : ℕ) : (∫ ω, M.exponential a N ω ∂μ) = 1 := by
  have hh := integral_congr_ae ((M.martingale a).2 0 N (Nat.zero_le N))
  rw [integral_condExp (F.le 0)] at hh
  simpa [exponential, sumIncrement, sumVariance] using hh

/-- A bound on total predictable energy gives a dimension-free L2
bound on the normalized exponential. This is the uniform-integrability
estimate needed when the simple-input approximation is removed. -/
theorem square_integral_le (a : ℝ) (N : ℕ) (K : ℝ)
    (hcap : ∀ᵐ ω ∂μ, M.sumVariance N ω ≤ K) :
    Integrable (fun ω ↦ M.exponential a N ω ^ 2) μ ∧
      (∫ ω, M.exponential a N ω ^ 2 ∂μ) ≤ Real.exp (a ^ 2 * K) := by
  have hb : ∀ᵐ ω ∂μ, M.exponential a N ω ^ 2 ≤
      Real.exp (a ^ 2 * K) * M.exponential (2 * a) N ω := by
    filter_upwards [hcap] with ω hω
    dsimp [exponential]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hω (sq_nonneg a)]
  have hi := (M.exponential_integrable (2 * a) N).const_mul (Real.exp (a ^ 2 * K))
  have hs : Integrable (fun ω ↦ M.exponential a N ω ^ 2) μ := by
    apply hi.mono' (((M.exponential_adapted a N).mono (F.le N)).pow 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    change ‖M.exponential a N ω ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hω
  refine ⟨hs, ?_⟩
  have hh := integral_mono_ae hs hi hb
  rw [integral_const_mul, M.integral_eq_one (2 * a) N, mul_one] at hh
  exact hh

end Model
end SHEStochastic.DiscreteGaussianExponential
