module

public import SHE.HeatChain
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Collision-uniform Gaussian localization of finite compact heat clusters.
The common annihilator and its full-nullspace envelope are both proved inputs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatSpanCluster
open MeasureTheory Set SHE.HeatAnnihilator SHE.HeatFactor SHE.HeatChain
open scoped ContDiff

def realFirstOrder (p : Parameter) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x + (2 * p.1 * (x : ℂ) - p.2) * f x

theorem contDiff_realFirstOrder (p : Parameter) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (realFirstOrder p f) := by
  have hreal : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hcoef : ContDiff ℝ ∞ (fun x : ℝ => 2 * p.1 * (x : ℂ) - p.2) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => 2 * p.1)).mul hreal).sub contDiff_const
  exact (contDiff_infty_iff_deriv.mp hf).2.add (hcoef.mul hf)

def realWordApply : (n : ℕ) → (Fin n → Parameter) → (ℝ → ℂ) → ℝ → ℂ
  | 0, _, f => f
  | n + 1, p, f => realWordApply n (Fin.tail p) (realFirstOrder (p 0) f)

/-- Every actual smooth function killed by a factor word is one of the
explicit finite-chain solutions; no existence/uniqueness axiom is used. -/
theorem exists_chainSolve_of_realWordApply_zero (n : ℕ) (p : Fin n → Parameter)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hzero : realWordApply n p f = 0) :
    ∃ c : Fin n → ℂ, chainSolve n p c = f := by
  induction n generalizing f with
  | zero => exact ⟨0, hzero.symm⟩
  | succ n ih =>
    let g := realFirstOrder (p 0) f
    have hg : ContDiff ℝ ∞ g := contDiff_realFirstOrder (p 0) hf
    obtain ⟨c, hc⟩ := ih (Fin.tail p) g hg hzero
    refine ⟨Fin.cons (f 0) c, ?_⟩
    change factorSolve (p 0) (f 0) (chainSolve n (Fin.tail p) c) = f
    rw [hc]
    apply factorSolve_eq_of_hasDerivAt (p 0) f g hg.continuous
    intro x
    have hd := ((contDiff_infty_iff_deriv.mp hf).1 x).hasDerivAt
    convert! hd using 1
    dsimp only [g, realFirstOrder]
    ring

theorem bounded_realWord_gaussian_envelope (n : ℕ) (R : ℝ) {γ k B : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin n → Parameter), ‖p‖ ≤ R →
      (∀ i, γ + k ≤ (p i).1.re) → (∀ i, |(p i).2.re| ≤ B) →
      ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f → realWordApply n p f = 0 →
      ∀ x : ℝ, ‖f x‖ ^ 2 ≤ C * (∫ u in Icc (-1 : ℝ) 1, ‖f u‖ ^ 2) *
        Real.exp (-(2 * γ) * x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := bounded_chain_gaussian_envelope n R hk
  refine ⟨C, hC, ?_⟩
  intro p hp ha hb f hf hzero x
  obtain ⟨c, hc⟩ := exists_chainSolve_of_realWordApply_zero n p f hf hzero
  have h := hbound p hp ha hb c x
  simpa only [localEnergy, hc] using h

theorem contDiff_firstOrder (p : Parameter) {f : ℂ → ℂ} (hf : ContDiff ℂ ∞ f) :
    ContDiff ℂ ∞ (firstOrder p f) := by
  have hcoef : ContDiff ℂ ∞ (fun z : ℂ => 2 * p.1 * z - p.2) := by fun_prop
  exact (contDiff_infty_iff_deriv.mp hf).2.add (hcoef.mul hf)

theorem realFirstOrder_restrict (p : Parameter) {f : ℂ → ℂ} (hf : ContDiff ℂ ∞ f) :
    realFirstOrder p (fun x : ℝ => f (x : ℂ)) = fun x : ℝ => firstOrder p f (x : ℂ) := by
  funext x
  unfold realFirstOrder firstOrder
  rw [(((contDiff_infty_iff_deriv.mp hf).1 (x : ℂ)).hasDerivAt).comp_ofReal.deriv]

theorem realWordApply_restrict (n : ℕ) (p : Fin n → Parameter) (f : ℂ → ℂ)
    (hf : ContDiff ℂ ∞ f) :
    realWordApply n p (fun x : ℝ => f (x : ℂ)) =
      fun x : ℝ => wordApply (List.ofFn p) f (x : ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change realWordApply n (Fin.tail p) (realFirstOrder (p 0) (fun x : ℝ => f (x : ℂ))) = _
    rw [realFirstOrder_restrict (p 0) hf, ih _ _ (contDiff_firstOrder (p 0) hf)]
    simp only [List.ofFn_succ, wordApply, List.foldl_cons]
    rfl

theorem contDiff_gaussian (p : Parameter) : ContDiff ℂ ∞ (gaussian p) := by
  unfold gaussian
  fun_prop

theorem contDiff_gaussian_span {q : ℕ} (base : Fin q → Parameter) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i)))) : ContDiff ℂ ∞ f := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  rw [← hc]
  convert! ContDiff.sum (s := Finset.univ)
    (fun i _ => (contDiff_gaussian (base i)).const_smul (c i)) using 1
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem realWordApply_annihilator {q : ℕ} (base : Fin q → Parameter) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i)))) :
    let word := annihilatorWord (List.ofFn base)
    realWordApply word.length word.get (fun x : ℝ => f (x : ℂ)) = 0 := by
  dsimp only
  rw [realWordApply_restrict _ _ _ (contDiff_gaussian_span base f hf), List.ofFn_get]
  have hzero := annihilatorWord_span base (List.ofFn base)
    (fun i => List.mem_ofFn.mpr ⟨i, rfl⟩) f hf
  rw [hzero]
  rfl

/-- The compact-cluster span estimate is an actual theorem for arbitrary
finite Gaussian generators with bounded complex parameters. It includes all
coalescences without any lower bound on a Gram eigenvalue. -/
theorem bounded_gaussian_span_local_envelope (q : ℕ) (R : ℝ) {γ k B : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (base : Fin q → Parameter), ‖base‖ ≤ R →
      (∀ i, γ + k ≤ (base i).1.re) → (∀ i, |(base i).2.re| ≤ B) →
      ∀ (f : ℂ → ℂ), f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i))) →
      ∀ x : ℝ, ‖f (x : ℂ)‖ ^ 2 ≤ C * (∫ u in Icc (-1 : ℝ) 1, ‖f (u : ℂ)‖ ^ 2) *
        Real.exp (-(2 * γ) * x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := bounded_realWord_gaussian_envelope (2 ^ q - 1) R (γ := γ) (B := B) hk
  refine ⟨C, hC, ?_⟩
  intro base hbase ha hb f hf x
  let word := annihilatorWord (List.ofFn base)
  have hlen : word.length = 2 ^ q - 1 := by
    have h := annihilatorWord_length (List.ofFn base)
    simp only [List.length_ofFn] at h
    dsimp only [word]
    omega
  have hmem : ∀ j : Fin word.length, ∃ i : Fin q, base i = word.get j := by
    intro j
    apply List.mem_ofFn.mp
    exact annihilatorWord_mem (List.ofFn base) (word.get j) (List.get_mem word j)
  have hR : 0 ≤ R := (norm_nonneg base).trans hbase
  have hword : ‖word.get‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    obtain ⟨i, hi⟩ := hmem j
    rw [← hi]
    exact (norm_le_pi_norm base i).trans hbase
  have hwa : ∀ j : Fin word.length, γ + k ≤ (word.get j).1.re := by
    intro j
    obtain ⟨i, hi⟩ := hmem j
    rw [← hi]
    exact ha i
  have hwb : ∀ j : Fin word.length, |(word.get j).2.re| ≤ B := by
    intro j
    obtain ⟨i, hi⟩ := hmem j
    rw [← hi]
    exact hb i
  have hreal : ContDiff ℝ ∞ (fun u : ℝ => f (u : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      ((contDiff_gaussian_span base f hf).restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hboundW := hbound
  rw [← hlen] at hboundW
  exact hboundW word.get hword hwa hwb (fun u : ℝ => f (u : ℂ)) hreal
    (realWordApply_annihilator base f hf) x

/-- The compact-cluster estimate with its genuine global line L² energy.
Global integrability is proved from the local estimate, rather than assumed. -/
theorem bounded_gaussian_span_global_envelope (q : ℕ) (R : ℝ) {γ k B : ℝ}
    (hγ : 0 < γ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (base : Fin q → Parameter), ‖base‖ ≤ R →
      (∀ i, γ + k ≤ (base i).1.re) → (∀ i, |(base i).2.re| ≤ B) →
      ∀ (f : ℂ → ℂ), f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i))) →
      Integrable (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) ∧
      ∀ x : ℝ, ‖f (x : ℂ)‖ ^ 2 ≤ C * (∫ u : ℝ, ‖f (u : ℂ)‖ ^ 2) *
        Real.exp (-(2 * γ) * x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := bounded_gaussian_span_local_envelope q R (γ := γ) (B := B) hk
  refine ⟨C, hC, ?_⟩
  intro base hbase ha hb f hf
  let E : ℝ := ∫ u in Icc (-1 : ℝ) 1, ‖f (u : ℂ)‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hbnd := hbound base hbase ha hb f hf
  have hcont : Continuous (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) :=
    (((contDiff_gaussian_span base f hf).continuous.comp Complex.continuous_ofReal).norm.pow 2)
  have hi : Integrable (fun u : ℝ => ‖f (u : ℂ)‖ ^ 2) := by
    apply ((integrable_exp_neg_mul_sq (show 0 < 2 * γ by positivity)).const_mul (C * E)).mono'
      hcont.aestronglyMeasurable
    exact ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbnd u)
  refine ⟨hi, ?_⟩
  intro x
  have hlocal : E ≤ ∫ u : ℝ, ‖f (u : ℂ)‖ ^ 2 :=
    setIntegral_le_integral hi (ae_of_all _ (fun _ => sq_nonneg _))
  exact (hbnd x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlocal hC.le)
    (Real.exp_pos _).le)

end SHE.HeatSpanCluster
