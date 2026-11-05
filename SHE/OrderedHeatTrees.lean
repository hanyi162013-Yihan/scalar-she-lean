module

public import SHE.NativeHeatAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.OrderedHeatTrees
open Set MeasureTheory StoppedFourier NativeHeatAction NativeHeatSpan
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- Each new vertex chooses one original earlier parent. All edges are
the actual positive native heat kernels at their specified physical ages. -/
inductive Tree : ℕ → Type
  | root : Tree 0
  | branch {n : ℕ} (previous : Tree n) (parent : Fin (n+1)) (gap : ℝ)
      (positive : 0 < gap) : Tree (n+1)

def age : {n : ℕ} → Tree n → Fin (n+1) → ℝ
  | _,.root => fun _ => 0
  | _,.branch T parent gap _ => Fin.snoc (age T) (age T parent+gap)

theorem age_nonneg {n : ℕ} (T : Tree n) (i : Fin (n+1)) : 0 ≤ age T i := by
  induction T with
  | root => exact le_rfl
  | branch T parent gap hg ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [age,Fin.snoc_last] using add_nonneg (ih parent) hg.le
    · simpa only [age,Fin.snoc_castSucc] using ih j

/-- Literal iterated spatial integration over every nonroot vertex. -/
def average : {n : ℕ} → Tree n → ((Fin (n+1) → HeatCircle) → ℝ) → HeatCircle → ℝ
  | _,.root,F,a => F (fun _ => a)
  | _,.branch T parent gap hg,F,a =>
      average T (fun z => action gap hg (fun y => F (Fin.snoc z y)) (z parent)) a

theorem average_const {n : ℕ} (T : Tree n) (b : ℝ) (a : HeatCircle) :
    average T (fun _ => b) a = b := by
  induction T with
  | root => rfl
  | branch T parent gap hg ih =>
    simpa only [average,action_const] using ih

/-- Every branch off the selected endpoint's ancestor path integrates to
one. Consecutive path edges convolve at their exact summed physical age.
This holds for every finite ordered tree, with arbitrary parent choices. -/
theorem endpoint_kernel {n : ℕ} (T : Tree n) (i : Fin (n+1))
    {r : ℝ} (hr : 0 < r) (a b : HeatCircle) :
    average T (fun z => edge r hr (z i) b) a =
      edge (age T i+r) (add_pos_of_nonneg_of_pos (age_nonneg T i) hr) a b := by
  induction T generalizing r with
  | root => simp only [average,age,zero_add]
  | branch T parent gap hg ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change average T (fun z => action gap hg
        (fun y => edge r hr ((Fin.snoc z y : Fin (_+2) → HeatCircle) (Fin.last _)) b) (z parent)) a = _
      simp only [Fin.snoc_last]
      have he : (fun z : Fin (_+1) → HeatCircle =>
          action gap hg (fun y => edge r hr y b) (z parent)) =
          fun z => edge (gap+r) (add_pos hg hr) (z parent) b := by
        funext z
        exact kernel_norm_convolution hg hr (z parent) b
      rw [he,ih parent (add_pos hg hr)]
      simp only [age,Fin.snoc_last,add_assoc]
    · change average T (fun z => action gap hg
        (fun y => edge r hr ((Fin.snoc z y : Fin (_+2) → HeatCircle) j.castSucc) b) (z parent)) a = _
      simp only [Fin.snoc_castSucc,action_const]
      rw [ih j hr]
      simp only [age,Fin.snoc_castSucc]

end SHE.OrderedHeatTrees
