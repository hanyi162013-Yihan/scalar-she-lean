module

public import SHEStochastic.PastedGeneratorFunctional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.PastedPastTests
open StoppedPathPasting PastedGeneratorFunctional
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] (H : ℝ≥0)

/-- A path test uses only the trajectory through s. This formulation
also covers ordinary finite cylinder tests of past evaluations. -/
def UsesPast (s : Time H) (test : Path H E → ℝ) : Prop :=
  ∀ x y : Path H E, (∀ t : Time H, t.val ≤ s.val → x t = y t) → test x = test y

theorem value_usesPast (f b : E → ℝ) (q : Time H) :
    UsesPast H q (fun x ↦ value H f b x q) := by
  intro x y hxy
  have hi : (∫ s in 0..q.val, b (read H x s)) = ∫ s in 0..q.val, b (read H y s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le q.property.1
    intro s hs
    have hsH : s ∈ Set.Icc (0 : ℝ) H := ⟨hs.1.le, hs.2.le.trans q.property.2⟩
    change b (read H x (⟨s, hsH⟩ : Time H).val) = b (read H y (⟨s, hsH⟩ : Time H).val)
    rw [read_val, read_val, hxy ⟨s, hsH⟩ hs.2.le]
  simp only [value, hxy q le_rfl, hxy (origin H) q.property.1, hi]

theorem test_before (s r : Time H) (test : Path H E → ℝ) (htest : UsesPast H s test)
    (x y : Path H E) (hs : s.val ≤ r.val) : test (paste H r x y) = test x :=
  htest _ _ (fun t ht ↦ paste_before H r t x y (ht.trans hs))

/-- On the event where the stopped increment is nonzero, the join is
after s, so the enlarged past test is exactly an original past test. -/
theorem test_of_pre_nonzero (f b : E → ℝ) (s t r : Time H)
    (hst : s.val ≤ t.val) (test : Path H E → ℝ) (htest : UsesPast H s test)
    (x y : Path H E)
    (hne : value H f b x (pastTime H r t) - value H f b x (pastTime H r s) ≠ 0) :
    test (paste H r x y) = test x := by
  apply test_before H s r test htest x y
  apply le_of_not_gt
  intro hrs
  have hs : pastTime H r s = r := Subtype.ext (min_eq_right hrs.le)
  have ht : pastTime H r t = r := Subtype.ext (min_eq_right (hrs.le.trans hst))
  exact hne (by rw [hs, ht, sub_self])

/-- For each fixed original trajectory and join, an enlarged test of
the past through s depends on the future only through (s-r)+. -/
theorem shifted_test (s r : Time H) (test : Path H E → ℝ)
    (htest : UsesPast H s test) (x : Path H E) :
    UsesPast H (futureTime H r s) (fun y ↦ test (paste H r x y)) := by
  intro y z he
  apply htest
  intro t ht
  have hmono : (futureTime H r t).val ≤ (futureTime H r s).val :=
    max_le_max_right _ (sub_le_sub_right ht _)
  have hzero : (origin H).val ≤ (futureTime H r s).val :=
    (futureTime H r s).property.1
  rw [paste_apply, paste_apply, he (futureTime H r t) hmono, he (origin H) hzero]

end SHEStochastic.PastedPastTests
