module

public import SHE.HeatFactor
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-! Finite stable-factor chains and collision-uniform local L² observability.
Every solution family here is constructed by actual variation of constants. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatChain
open MeasureTheory Set SHE.HeatAnnihilator SHE.HeatFactor
open scoped Topology

def chainSolve : (n : ℕ) → (Fin n → Parameter) → (Fin n → ℂ) → ℝ → ℂ
  | 0, _, _ => fun _ => 0
  | n + 1, p, c => factorSolve (p 0) (c 0) (chainSolve n (Fin.tail p) (Fin.tail c))

theorem continuous_chainSolve (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ) :
    Continuous (chainSolve n p c) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact continuous_factorSolve _ _ _ (ih (Fin.tail p) (Fin.tail c))

theorem continuous_chainSolve_family {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (n : ℕ) (p : X → Fin n → Parameter) (c : X → Fin n → ℂ)
    (hp : Continuous p) (hc : Continuous c) :
    Continuous (fun q : X × ℝ => chainSolve n (p q.1) (c q.1) q.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hpt : Continuous (fun x => Fin.tail (p x)) :=
      continuous_pi (fun i => (continuous_apply i.succ).comp hp)
    have hct : Continuous (fun x => Fin.tail (c x)) :=
      continuous_pi (fun i => (continuous_apply i.succ).comp hc)
    exact continuous_factorSolve_family (fun x => p x 0) (fun x => c x 0)
      (fun x => chainSolve n (Fin.tail (p x)) (Fin.tail (c x)))
      ((continuous_apply 0).comp hp) ((continuous_apply 0).comp hc)
      (ih _ _ hpt hct)

theorem continuous_chainSolve_joint (n : ℕ) :
    Continuous (fun q : ((Fin n → Parameter) × (Fin n → ℂ)) × ℝ =>
      chainSolve n q.1.1 q.1.2 q.2) :=
  continuous_chainSolve_family n Prod.fst Prod.snd continuous_fst continuous_snd

theorem factorSolve_smul (p : Parameter) (a c : ℂ) (g : ℝ → ℂ) :
    factorSolve p (a * c) (fun u => a * g u) = fun x => a * factorSolve p c g x := by
  funext x
  have h : (fun u => realGaussian (-p) u * (a * g u)) =
      fun u => a * (realGaussian (-p) u * g u) := by funext u; ring
  unfold factorSolve
  rw [h, intervalIntegral.integral_const_mul]
  ring

theorem chainSolve_smul (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ) (a : ℂ) :
    chainSolve n p (a • c) = a • chainSolve n p c := by
  induction n with
  | zero => funext x; simp [chainSolve]
  | succ n ih =>
    change factorSolve (p 0) (a * c 0) (chainSolve n (Fin.tail p) (a • Fin.tail c)) = _
    rw [ih]
    exact factorSolve_smul (p 0) a (c 0) (chainSolve n (Fin.tail p) (Fin.tail c))

/-- The observed first component determines every initial chain coordinate.
This holds on a fixed local interval, without any separation assumption. -/
theorem chainSolve_initial_eq_zero_of_local_zero (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ)
    (hzero : ∀ x ∈ Ioo (-1 : ℝ) 1, chainSolve n p c x = 0) : c = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hhead : c 0 = 0 := by
      simpa only [chainSolve, factorSolve_zero] using hzero 0 (by constructor <;> norm_num)
    have htail : ∀ x ∈ Ioo (-1 : ℝ) 1,
        chainSolve n (Fin.tail p) (Fin.tail c) x = 0 := by
      intro x hx
      have hd := hasDerivAt_factorSolve (p 0) (c 0) (chainSolve n (Fin.tail p) (Fin.tail c))
        (continuous_chainSolve _ _ _) x
      have he : chainSolve (n + 1) p c =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hzero y hy
      have hz := (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq he
      have hh := hd.unique hz
      change chainSolve n (Fin.tail p) (Fin.tail c) x -
        (2 * (p 0).1 * (x : ℂ) - (p 0).2) * chainSolve (n + 1) p c x = 0 at hh
      rw [hzero x hx, mul_zero, sub_zero] at hh
      exact hh
    have hc := ih (Fin.tail p) (Fin.tail c) htail
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hhead
    · exact congrFun hc j

def localEnergy (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ) : ℝ :=
  ∫ x in Icc (-1 : ℝ) 1, ‖chainSolve n p c x‖ ^ 2

theorem localEnergy_nonneg (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ) :
    0 ≤ localEnergy n p c := integral_nonneg (fun _ => sq_nonneg _)

theorem continuous_localEnergy (n : ℕ) :
    Continuous (fun q : (Fin n → Parameter) × (Fin n → ℂ) => localEnergy n q.1 q.2) :=
  continuous_parametric_integral_of_continuous ((continuous_chainSolve_joint n).norm.pow 2) isCompact_Icc

theorem localEnergy_pos (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ) (hc : c ≠ 0) :
    0 < localEnergy n p c := by
  have hex : ∃ x ∈ Ioo (-1 : ℝ) 1, chainSolve n p c x ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (chainSolve_initial_eq_zero_of_local_zero n p c h)
  obtain ⟨x, hx, hfx⟩ := hex
  have hi := intervalIntegral.integral_pos (by norm_num : (-1 : ℝ) < 1)
    (((continuous_chainSolve n p c).norm.pow 2).continuousOn)
    (fun _ _ => sq_nonneg _)
    ⟨x, ⟨hx.1.le, hx.2.le⟩, pow_pos (norm_pos_iff.mpr hfx) 2⟩
  unfold localEnergy
  rwa [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

theorem localEnergy_smul (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ) (a : ℂ) :
    localEnergy n p (a • c) = ‖a‖ ^ 2 * localEnergy n p c := by
  unfold localEnergy
  simp_rw [chainSolve_smul, Pi.smul_apply, norm_smul, mul_pow]
  exact integral_const_mul _ _

/-- The compact-family local L² observability estimate used in the manuscript
is proved by an actual compact minimum of the constructed solution family.
No separation of parameters or nondegeneracy of the generator Gram is used. -/
theorem compact_chain_observability (n : ℕ) (K : Set (Fin n → Parameter)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ c : Fin n → ℂ, ‖c‖ ^ 2 ≤ C * localEnergy n p c := by
  let S := K ×ˢ Metric.sphere (0 : Fin n → ℂ) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  obtain ⟨ε, hε, he⟩ := hS.exists_forall_le' (continuous_localEnergy n).continuousOn
    (a := 0) (by
      intro q hq
      have hn : ‖q.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hq.2
      apply localEnergy_pos n q.1 q.2
      intro hzero
      rw [hzero, norm_zero] at hn
      norm_num at hn)
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro p hp c
  by_cases hc : c = 0
  · rw [hc, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (inv_nonneg.mpr hε.le) (localEnergy_nonneg n p 0)
  · have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    let a : ℂ := ((‖c‖)⁻¹ : ℝ)
    let d : Fin n → ℂ := a • c
    have ha : ‖a‖ = ‖c‖⁻¹ := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    have hd : ‖d‖ = 1 := by
      dsimp only [d]
      rw [norm_smul, ha, inv_mul_cancel₀ hnorm.ne']
    have hmem : (p, d) ∈ S := ⟨hp, by simpa only [Metric.mem_sphere, dist_zero_right] using hd⟩
    have hlower := he (p, d) hmem
    change ε ≤ localEnergy n p (a • c) at hlower
    rw [localEnergy_smul, ha] at hlower
    have hmul := mul_le_mul_of_nonneg_right hlower (sq_nonneg ‖c‖)
    have hcancel : (‖c‖⁻¹ ^ 2 * localEnergy n p c) * ‖c‖ ^ 2 = localEnergy n p c := by
      field_simp
    rw [hcancel] at hmul
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hε).mpr (by nlinarith)

theorem bounded_chain_observability (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin n → Parameter), ‖p‖ ≤ R →
      ∀ c : Fin n → ℂ, ‖c‖ ^ 2 ≤ C * localEnergy n p c := by
  obtain ⟨C, hC, hb⟩ := compact_chain_observability n (Metric.closedBall 0 R) (isCompact_closedBall _ _)
  exact ⟨C, hC, fun p hp c => hb p (by simpa only [Metric.mem_closedBall, dist_zero_right] using hp) c⟩

def stableFactorConstant (k B : ℝ) : ℝ :=
  Real.exp (B ^ 2 / (2 * k)) + (∫ v, tailKernel k B v) + 1

theorem stableFactorConstant_bounds (k B : ℝ) :
    1 ≤ stableFactorConstant k B ∧
    Real.exp (B ^ 2 / (2 * k)) ≤ stableFactorConstant k B ∧
    (∫ v, tailKernel k B v) ≤ stableFactorConstant k B := by
  have hI : 0 ≤ ∫ v, tailKernel k B v := integral_nonneg (fun v => tailKernel_nonneg k B v)
  have hE := Real.exp_pos (B ^ 2 / (2 * k))
  unfold stableFactorConstant
  constructor <;> [skip; constructor] <;> linarith

/-- Arbitrarily long but finite stable-factor chains have a fixed weakened
Gaussian envelope, with an explicit constant independent of collisions. -/
theorem chainSolve_gaussian_bound (n : ℕ) (p : Fin n → Parameter) (c : Fin n → ℂ)
    {γ k B : ℝ} (hk : 0 < k) (ha : ∀ i, γ + k ≤ (p i).1.re)
    (hb : ∀ i, |(p i).2.re| ≤ B) (x : ℝ) :
    ‖chainSolve n p c x‖ ≤ stableFactorConstant k B ^ n *
      (∑ i, ‖c i‖) * Real.exp (-γ * x ^ 2) := by
  induction n generalizing x with
  | zero => simp [chainSolve]
  | succ n ih =>
    let A := stableFactorConstant k B
    let M := A ^ n * ∑ i : Fin n, ‖Fin.tail c i‖
    have hA := stableFactorConstant_bounds k B
    have hA0 : 0 ≤ A := le_trans (by norm_num) hA.1
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have htail : ∀ u, ‖chainSolve n (Fin.tail p) (Fin.tail c) u‖ ≤ M * Real.exp (-γ * u ^ 2) :=
      fun u => ih (Fin.tail p) (Fin.tail c) (fun i => ha i.succ) (fun i => hb i.succ) u
    have hfactor := factorSolve_gaussian_bound (p 0) (c 0)
      (chainSolve n (Fin.tail p) (Fin.tail c)) (continuous_chainSolve _ _ _)
      hk hM (ha 0) (hb 0) htail x
    have hpow : 1 ≤ A ^ n := one_le_pow₀ hA.1
    have hcoef : Real.exp (B ^ 2 / (2 * k)) * ‖c 0‖ + M * (∫ v, tailKernel k B v) ≤
        A ^ (n + 1) * (‖c 0‖ + ∑ i : Fin n, ‖Fin.tail c i‖) := by
      have h1 := mul_le_mul_of_nonneg_right hA.2.1 (norm_nonneg (c 0))
      have h2 := mul_le_mul_of_nonneg_left hA.2.2 hM
      have h3 := mul_le_mul_of_nonneg_right hpow (norm_nonneg (c 0))
      have h4 := mul_le_mul_of_nonneg_left h3 hA0
      have h4' : A * ‖c 0‖ ≤ A * (A ^ n * ‖c 0‖) := by simpa only [one_mul] using h4
      calc
        _ ≤ A * ‖c 0‖ + M * A := add_le_add h1 h2
        _ ≤ A * (A ^ n * ‖c 0‖) + M * A := add_le_add h4' (by rfl)
        _ = _ := by
          dsimp only [M]
          rw [pow_succ A n]
          ring
    change ‖factorSolve (p 0) (c 0) (chainSolve n (Fin.tail p) (Fin.tail c)) x‖ ≤ _
    rw [Fin.sum_univ_succ]
    exact hfactor.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)

/-- Compact bounded families of finite stable-factor nullspaces have the
collision-uniform Gaussian localization claimed for compact heat clusters. -/
theorem bounded_chain_gaussian_envelope (n : ℕ) (R : ℝ) {γ k B : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin n → Parameter), ‖p‖ ≤ R →
      (∀ i, γ + k ≤ (p i).1.re) → (∀ i, |(p i).2.re| ≤ B) →
      ∀ (c : Fin n → ℂ) (x : ℝ), ‖chainSolve n p c x‖ ^ 2 ≤
        C * localEnergy n p c * Real.exp (-(2 * γ) * x ^ 2) := by
  obtain ⟨D, hD, hObs⟩ := bounded_chain_observability n R
  let A := stableFactorConstant k B ^ n * (n : ℝ)
  have hA0 : 0 ≤ A := by
    have h := (stableFactorConstant_bounds k B).1
    dsimp [A]
    positivity
  refine ⟨A ^ 2 * D + 1, by positivity, ?_⟩
  intro p hp ha hb c x
  have hsum : (∑ i, ‖c i‖) ≤ (n : ℝ) * ‖c‖ := by
    simpa only [Fintype.card_fin, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm c
  have hpoint : ‖chainSolve n p c x‖ ≤ A * ‖c‖ * Real.exp (-γ * x ^ 2) := by
    have h := chainSolve_gaussian_bound n p c hk ha hb x
    have hconst : 0 ≤ stableFactorConstant k B ^ n :=
      pow_nonneg ((stableFactorConstant_bounds k B).1.trans' (by norm_num)) _
    have hm := mul_le_mul_of_nonneg_left hsum hconst
    have hh := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-γ * x ^ 2)).le
    exact h.trans (by convert! hh using 1; dsimp only [A]; ring)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ A * ‖c‖ * Real.exp (-γ * x ^ 2))).mpr hpoint
  have hexp : Real.exp (-γ * x ^ 2) ^ 2 = Real.exp (-(2 * γ) * x ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, hexp] at hsq
  have hO := hObs p hp c
  have hE := localEnergy_nonneg n p c
  have hmul := mul_le_mul_of_nonneg_left hO
    (mul_nonneg (sq_nonneg A) (Real.exp_pos (-(2 * γ) * x ^ 2)).le)
  nlinarith [mul_nonneg hE (Real.exp_pos (-(2 * γ) * x ^ 2)).le]

end SHE.HeatChain
