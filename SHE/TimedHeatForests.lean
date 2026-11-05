module

public import SHE.HeatForestProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

def rootValues {E : Type} {m : ℕ} : (k : ℕ) → (Fin (m+k) → E) → Fin m → E
  | 0,z => z
  | k+1,z => rootValues k (fun i => z i.succ)

/-- Exact original-time geometry, including arbitrary distinct initial
observation targets. The equality records each actual parent heat age. -/
def TimeCompatible {m : ℕ} (κ : ℝ) : {k : ℕ} → Forest m k → (Fin (m+k) → ℝ) → Prop
  | _,.roots,_ => True
  | _,.branch T parent gap _,t =>
      TimeCompatible κ T (fun i => t i.succ) ∧ gap=κ*(t parent.succ-t 0)

theorem age_eq_elapsed {m k : ℕ} {κ : ℝ} (T : Forest m k) (t : Fin (m+k) → ℝ)
    (ht : TimeCompatible κ T t) (i : Fin (m+k)) :
    age T i = κ*(rootValues k t (rootOf T i)-t i) := by
  induction T with
  | roots => simp only [age,rootOf,rootValues,sub_self,mul_zero]
  | branch T parent gap hg ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [age,rootOf,Fin.cons_zero,rootValues]
      rw [ih _ ht.1,ht.2]
      ring
    · simpa only [age,rootOf,Fin.cons_succ,rootValues] using ih _ ht.1 j

theorem elapsed_pos {m k : ℕ} {κ : ℝ} (hκ : 0 < κ) (T : Forest m k)
    (t : Fin (m+k) → ℝ) (ht : TimeCompatible κ T t) (i : Fin (m+k))
    {q : ℝ} (hq : q < t i) : 0 < κ*(rootValues k t (rootOf T i)-q) := by
  have hh := add_pos_of_nonneg_of_pos (age_nonneg T i) (mul_pos hκ (sub_pos.mpr hq))
  simp only [age_eq_elapsed T t ht] at hh
  convert! hh using 1
  ring

/-- The genuine product Haar integral keeps the true original ancestor
root and its target time. No common-time or common-center assumption is
imposed on the initial finite cylinder. -/
theorem integral_timed_endpoint {m k : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (T : Forest m k) (t : Fin (m+k) → ℝ) (ht : TimeCompatible κ T t)
    (i : Fin (m+k)) {q : ℝ} (hq : q < t i) (a : Fin m → HeatCircle) (b : HeatCircle) :
    (∫ x : Fin k → HeatCircle, density T (values a k x)*
      edge (κ*(t i-q)) (mul_pos hκ (sub_pos.mpr hq)) (values a k x i) b
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      edge (κ*(rootValues k t (rootOf T i)-q)) (elapsed_pos hκ T t ht i hq)
        (a (rootOf T i)) b := by
  have hh := integral_endpoint_kernel T i (mul_pos hκ (sub_pos.mpr hq)) a b
  simp only [age_eq_elapsed T t ht] at hh
  convert! hh using 1
  congr 1
  ring

end SHE.OrderedHeatForests
