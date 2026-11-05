module

public import SHE.HeatTreeEndpoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.OrderedHeatForests
open Set MeasureTheory StoppedFourier NativeHeatAction
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] NativeHeatAction.edge NativeHeatSpan.kernel

/-- The original finite observation frame may contain many distinct
roots. Each insertion uses one genuinely earlier observation as parent;
the newest vertex is coordinate zero, as in the stochastic word. -/
inductive Forest (m : ℕ) : ℕ → Type
  | roots : Forest m 0
  | branch {k : ℕ} (previous : Forest m k) (parent : Fin (m+k))
      (gap : ℝ) (positive : 0 < gap) : Forest m (k+1)

def values {E : Type} {m : ℕ} (a : Fin m → E) : (k : ℕ) → (Fin k → E) → Fin (m+k) → E
  | 0,_ => a
  | k+1,x => Fin.cons (x 0) (values a k (fun i => x i.succ))

theorem values_cons {E : Type} {m k : ℕ} (a : Fin m → E) (x : Fin k → E) (y : E) :
    values a (k+1) (Fin.cons y x) = Fin.cons y (values a k x) := by
  simp only [values,Fin.cons_zero,Fin.cons_succ]

def rootOf {m : ℕ} : {k : ℕ} → Forest m k → Fin (m+k) → Fin m
  | _,.roots => fun i => i
  | _,.branch T parent _ _ => Fin.cons (rootOf T parent) (rootOf T)

def age {m : ℕ} : {k : ℕ} → Forest m k → Fin (m+k) → ℝ
  | _,.roots => fun _ => 0
  | _,.branch T parent gap _ => Fin.cons (age T parent+gap) (age T)

theorem age_nonneg {m k : ℕ} (T : Forest m k) (i : Fin (m+k)) : 0 ≤ age T i := by
  induction T with
  | roots => exact le_rfl
  | branch T parent gap hg ih =>
    exact Fin.cases (by simpa only [age,Fin.cons_zero] using add_nonneg (ih parent) hg.le)
      (fun j => by simpa only [age,Fin.cons_succ] using ih j) i

def average {m : ℕ} : {k : ℕ} → Forest m k →
    ((Fin (m+k) → HeatCircle) → ℝ) → (Fin m → HeatCircle) → ℝ
  | _,.roots,F,a => F a
  | _,.branch T parent gap hg,F,a =>
      average T (fun z => action gap hg (fun y => F (Fin.cons y z)) (z parent)) a

def density {m : ℕ} : {k : ℕ} → Forest m k → (Fin (m+k) → HeatCircle) → ℝ
  | _,.roots,_ => 1
  | _,.branch T parent gap hg,z =>
      density T (fun i => z i.succ)*edge gap hg (z parent.succ) (z 0)

theorem density_nonneg {m k : ℕ} (T : Forest m k) (z : Fin (m+k) → HeatCircle) :
    0 ≤ density T z := by
  induction T with
  | roots => exact zero_le_one
  | branch T parent gap hg ih =>
    exact mul_nonneg (ih _) (by unfold NativeHeatAction.edge; exact norm_nonneg _)

theorem density_cons {m k : ℕ} (T : Forest m k) (parent : Fin (m+k))
    {gap : ℝ} (hg : 0 < gap) (z : Fin (m+k) → HeatCircle) (y : HeatCircle) :
    density (.branch T parent gap hg) (Fin.cons y z) =
      density T z*edge gap hg (z parent) y := by
  simp only [density,Fin.cons_zero,Fin.cons_succ]

theorem average_const {m k : ℕ} (T : Forest m k) (b : ℝ) (a : Fin m → HeatCircle) :
    average T (fun _ => b) a = b := by
  induction T with
  | roots => rfl
  | branch T parent gap hg ih => simpa only [average,action_const] using ih

/-- All off-path branches integrate to one, leaving the actual root of
the selected terminal vertex. Distinct original root locations are kept. -/
theorem endpoint_kernel {m k : ℕ} (T : Forest m k) (i : Fin (m+k))
    {r : ℝ} (hr : 0 < r) (a : Fin m → HeatCircle) (b : HeatCircle) :
    average T (fun z => edge r hr (z i) b) a =
      edge (age T i+r) (add_pos_of_nonneg_of_pos (age_nonneg T i) hr) (a (rootOf T i)) b := by
  induction T generalizing r with
  | roots => simp only [average,age,rootOf,zero_add]
  | @branch k T parent gap hg ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change average T (fun z => action gap hg
        (fun y => edge r hr ((Fin.cons y z : Fin (m+k+1) → HeatCircle) 0) b) (z parent)) a = _
      simp only [Fin.cons_zero]
      have he : (fun z : Fin (m+k) → HeatCircle =>
          action gap hg (fun y => edge r hr y b) (z parent)) =
          fun z => edge (gap+r) (add_pos hg hr) (z parent) b := by
        funext z
        simpa only [NativeHeatAction.action,NativeHeatAction.edge] using
          NativeHeatSpan.kernel_norm_convolution hg hr (z parent) b
      rw [he,ih parent (add_pos hg hr)]
      simp only [age,rootOf,Fin.cons_zero,add_assoc]
    · change average T (fun z => action gap hg
        (fun y => edge r hr ((Fin.cons y z : Fin (m+k+1) → HeatCircle) j.succ) b) (z parent)) a = _
      simp only [Fin.cons_succ,action_const]
      rw [ih j hr]
      simp only [age,rootOf,Fin.cons_succ]

end SHE.OrderedHeatForests
