module

public import SHEStochastic.PastedPastTests
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.PastedLinearHeatFunctional
open StoppedPathPasting PastedPastTests
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (lam : ℝ)

/-- Integrating-factor coordinate of a linear heat mode. -/
def value (x : Path H E) (t : Time H) : ℝ :=
  Real.exp (lam*t.val)*ell (x t)-ell (x (origin H))

@[simp] theorem value_origin (x : Path H E) : value H ell lam x (origin H) = 0 := by
  simp [value, origin]

theorem continuous_value : Continuous (fun p : Path H E × Time H ↦ value H ell lam p.1 p.2) := by
  unfold value
  fun_prop

def trajectory (x : Path H E) : C(Time H, ℝ) :=
  ⟨value H ell lam x, (continuous_value H ell lam).comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_trajectory : Continuous (trajectory H ell lam) :=
  ContinuousMap.continuous_of_continuous_uncurry (trajectory H ell lam) (continuous_value H ell lam)

/-- A fixed Borel path envelope, suitable for integrating uniformly
over conditional continuation laws without choosing random maxima. -/
def envelope (x : Path H E) : ℝ := ‖trajectory H ell lam x‖

theorem continuous_envelope : Continuous (envelope H ell lam) :=
  (continuous_trajectory H ell lam).norm

theorem value_bound (x : Path H E) (t : Time H) :
    ‖value H ell lam x t‖ ≤ envelope H ell lam x :=
  (trajectory H ell lam x).norm_coe_le_norm t

theorem envelope_attained (x : Path H E) :
    ∃ t : Time H, envelope H ell lam x = ‖value H ell lam x t‖ := by
  haveI : Nonempty (Time H) := ⟨origin H⟩
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (trajectory H ell lam x).continuous.norm.continuousOn
  refine ⟨t, le_antisymm ?_ (value_bound H ell lam x t)⟩
  exact ((trajectory H ell lam x).norm_le (norm_nonneg _)).mpr fun s ↦ ht (Set.mem_univ s)

theorem value_paste (r t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H ell lam (paste H r x y) t =
      value H ell lam x (pastTime H r t) + Real.exp (lam*r.val)*value H ell lam y (futureTime H r t) := by
  have hzero := paste_before H r (origin H) x y r.property.1
  by_cases ht : t.val ≤ r.val
  · have hp : pastTime H r t = t := Subtype.ext (min_eq_left ht)
    have hf : futureTime H r t = origin H := Subtype.ext (max_eq_right (sub_nonpos.mpr ht))
    rw [hp, hf, value_origin, mul_zero, add_zero]
    simp only [value, paste_before H r t x y ht, hzero]
  · have ht' := le_of_not_ge ht
    have hp : pastTime H r t = r := Subtype.ext (min_eq_right ht')
    have hf : (futureTime H r t).val = t.val-r.val := max_eq_left (sub_nonneg.mpr ht')
    have he : Real.exp (lam*t.val) = Real.exp (lam*r.val)*Real.exp (lam*(t.val-r.val)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [value, paste_after H r t x y ht' hjoin, hzero, hp, hf, hjoin, he]
    ring

/-- Linear heat coordinates concatenate with the deterministic
integrating factor at the join; no drift integral has to be reassembled. -/
theorem increment_paste (r s t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H ell lam (paste H r x y) t-value H ell lam (paste H r x y) s =
      (value H ell lam x (pastTime H r t)-value H ell lam x (pastTime H r s)) +
        Real.exp (lam*r.val)*(value H ell lam y (futureTime H r t)-value H ell lam y (futureTime H r s)) := by
  rw [value_paste H ell lam r t x y hjoin, value_paste H ell lam r s x y hjoin]
  ring

theorem test_of_pre_nonzero (s t r : Time H) (hst : s.val ≤ t.val)
    (test : Path H E → ℝ) (htest : UsesPast H s test) (x y : Path H E)
    (hne : value H ell lam x (pastTime H r t)-value H ell lam x (pastTime H r s) ≠ 0) :
    test (paste H r x y) = test x := by
  apply test_before H s r test htest x y
  apply le_of_not_gt
  intro hrs
  have hs : pastTime H r s = r := Subtype.ext (min_eq_right hrs.le)
  have ht : pastTime H r t = r := Subtype.ext (min_eq_right (hrs.le.trans hst))
  exact hne (by rw [hs, ht, sub_self])

end SHEStochastic.PastedLinearHeatFunctional
