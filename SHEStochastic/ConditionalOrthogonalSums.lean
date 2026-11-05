module

public import SHEStochastic.ConditionalBracket
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ConditionalOrthogonalSums
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A centered future L² variable is orthogonal to every past L² variable.
This is the existing conditional-expectation orthogonal projection theorem. -/
theorem inner_eq_zero {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (f g : Lp ℝ 2 μ)
    (hf : AEStronglyMeasurable[m] f μ)
    (hg : μ[(g : Ω → ℝ) | m] =ᵐ[μ] (fun _ ↦ 0)) : inner ℝ f g = 0 := by
  have hz : (condExpL2 ℝ ℝ hm g : Lp ℝ 2 μ) = 0 := by
    apply Lp.ext
    simpa only [Lp.toLp_coeFn] using
      (((Lp.memLp g).condExpL2_ae_eq_condExp (𝕜 := ℝ) hm).trans
        (hg.trans (Lp.coeFn_zero ℝ 2 μ).symm))
  calc
    _ = inner ℝ g f := real_inner_comm _ _
    _ = inner ℝ (condExpL2 ℝ ℝ hm g : Lp ℝ 2 μ) f :=
      (inner_condExpL2_eq_inner_fun hm g f hf).symm
    _ = 0 := by rw [hz, inner_zero_left]

/-- Pythagoras on any finite set of ordered, disjoint filtration intervals.
Only the selected indices require moment and adaptedness hypotheses. -/
theorem norm_sum_sq_intervals {κ T : Type*} [LinearOrder κ] [Preorder T] (F : Filtration T mΩ)
    (a b : κ → T) (A : κ → Lp ℝ 2 μ) (S : Finset κ)
    (hsep : ∀ k ∈ S, ∀ l ∈ S, k < l → b k ≤ a l)
    (hA : ∀ k ∈ S, AEStronglyMeasurable[F (b k)] (A k) μ)
    (hzero : ∀ k ∈ S, μ[(A k : Ω → ℝ) | F (a k)] =ᵐ[μ] (fun _ ↦ 0)) :
    ‖∑ k ∈ S, A k‖ ^ 2 = ∑ k ∈ S, ‖A k‖ ^ 2 := by
  classical
  have hcross (k : κ) (hk : k ∈ S) (l : κ) (hl : l ∈ S) (hne : k ≠ l) :
      inner ℝ (A k) (A l) = 0 := by
    rcases lt_or_gt_of_ne hne with hkl | hlk
    · exact inner_eq_zero (F.le (a l)) (A k) (A l)
        ((hA k hk).mono (F.mono (hsep k hk l hl hkl))) (hzero l hl)
    · rw [real_inner_comm]
      exact inner_eq_zero (F.le (a k)) (A l) (A k)
        ((hA l hl).mono (F.mono (hsep l hl k hk hlk))) (hzero k hk)
  calc
    _ = inner ℝ (∑ k ∈ S, A k) (∑ k ∈ S, A k) := (real_inner_self_eq_norm_sq _).symm
    _ = ∑ k ∈ S, ∑ l ∈ S, inner ℝ (A k) (A l) := by
      simp only [sum_inner, inner_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_eq_single k (fun l hl hlk ↦ hcross k hk l hl hlk.symm)
        (fun h ↦ False.elim (h hk)), real_inner_self_eq_norm_sq]

/-- Pythagoras for finite martingale differences in a discrete filtration. -/
theorem norm_sum_sq {F : Filtration ℕ mΩ} (A : ℕ → Lp ℝ 2 μ)
    (hA : ∀ k, AEStronglyMeasurable[F (k + 1)] (A k) μ)
    (hzero : ∀ k, μ[(A k : Ω → ℝ) | F k] =ᵐ[μ] (fun _ ↦ 0)) (S : Finset ℕ) :
    ‖∑ k ∈ S, A k‖ ^ 2 = ∑ k ∈ S, ‖A k‖ ^ 2 :=
  norm_sum_sq_intervals F id (fun k ↦ k + 1) A S
    (fun _ _ _ _ hkl ↦ Nat.succ_le_of_lt hkl) (fun k _ ↦ hA k) (fun k _ ↦ hzero k)

end SHEStochastic.ConditionalOrthogonalSums
