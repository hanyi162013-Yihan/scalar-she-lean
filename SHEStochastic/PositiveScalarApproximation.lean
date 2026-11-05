module

public import SHE.SmoothApproximation
public import SHE.CompatibleReference

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.PositiveScalarApproximation
open SHE Filter
open scoped NNReal Topology

theorem holder_of_bound {f : ℝ → ℝ} {C β : ℝ≥0}
    (h : ∀ x y, |f x-f y| ≤ C*|x-y|^(β : ℝ)) : HolderWith C β f := by
  intro x y
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (C : ℝ)*ENNReal.ofReal (dist x y)^(β : ℝ)
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y) (show 0 ≤ (β : ℝ) from β.2)]
  calc
    _ ≤ ENNReal.ofReal ((C : ℝ)*dist x y^(β : ℝ)) :=
      ENNReal.ofReal_le_ofReal (by simpa only [Real.dist_eq] using h x y)
    _ = _ := ENNReal.ofReal_mul (show 0 ≤ (C : ℝ) from C.2)

variable {a : ℝ → ℝ} {C β : ℝ≥0} (ha : HolderWith C β a) (hβ : 0 < β)
  (ell cap : ℝ) (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)

def variance (n : ℕ) : ℝ → ℝ := CompactMollifier.approximant a n
def amplitude (n : ℕ) (z : ℝ) : ℝ := Real.sqrt (variance (a := a) n z)
def root (z : ℝ) : ℝ := Real.sqrt (a z)
def rootConstant : ℝ≥0 := ⟨CompatibleReference.rootConstant ell, CompatibleReference.rootConstant_nonneg ell⟩
def bound : ℝ≥0 := ⟨Real.sqrt cap, Real.sqrt_nonneg cap⟩
def error (n : ℕ) : ℝ := CompatibleReference.rootConstant ell*C*CompactMollifier.radius n^(β : ℝ)

include hell hb in
theorem abs_bound (z : ℝ) : |a z| ≤ cap := by
  rw [abs_of_nonneg (hell.le.trans (hb z).1)]
  exact (hb z).2

include ha hβ hell hb in
theorem smooth (n : ℕ) : SmoothCylinders.BoundedSmooth (variance (a := a) n) :=
  CompactMollifier.approximant_boundedSmooth (ha.continuous hβ) (abs_bound ell cap hell hb) n

include ha hβ hell hb in
theorem bounds (n : ℕ) (z : ℝ) : ell ≤ variance (a := a) n z ∧ variance (a := a) n z ≤ cap :=
  CompactMollifier.approximant_elliptic (ha.continuous hβ) hell.le hb n z

include ha hβ hell hb in
theorem variance_holder (n : ℕ) : HolderWith C β (variance (a := a) n) := by
  apply holder_of_bound
  exact CompactMollifier.approximant_holder (ha.continuous hβ) (abs_bound ell cap hell hb)
    (fun x y ↦ by simpa only [Real.dist_eq] using ha.dist_le x y) n

include ha hβ hell hb in
theorem amplitude_holder (n : ℕ) :
    HolderWith (rootConstant ell*C) β (amplitude (a := a) n) := by
  apply holder_of_bound
  intro x y
  have hh := CompatibleReference.scalar_sqrt_lipschitz hell
    (bounds ha hβ ell cap hell hb n x).1 (bounds ha hβ ell cap hell hb n y).1
  have hv := (variance_holder ha hβ ell cap hell hb n).dist_le x y
  simp only [Real.dist_eq] at hv
  exact hh.trans ((mul_le_mul_of_nonneg_left hv (CompatibleReference.rootConstant_nonneg ell)).trans_eq
    (by change _ = (CompatibleReference.rootConstant ell*(C : ℝ))*|x-y|^(β : ℝ); ring))

include ha hβ hell hb in
theorem root_holder : HolderWith (rootConstant ell*C) β (root (a := a)) := by
  apply holder_of_bound
  intro x y
  have hh := CompatibleReference.scalar_sqrt_lipschitz hell (hb x).1 (hb y).1
  have hv := ha.dist_le x y
  simp only [Real.dist_eq] at hv
  exact hh.trans ((mul_le_mul_of_nonneg_left hv (CompatibleReference.rootConstant_nonneg ell)).trans_eq
    (by change _ = (CompatibleReference.rootConstant ell*(C : ℝ))*|x-y|^(β : ℝ); ring))

include ha hβ hell hb in
theorem amplitude_bound (n : ℕ) (z : ℝ) : ‖amplitude (a := a) n z‖ ≤ bound cap := by
  change ‖Real.sqrt (variance (a := a) n z)‖ ≤ Real.sqrt cap
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (bounds ha hβ ell cap hell hb n z).2

include hb in
theorem root_bound (z : ℝ) : ‖root (a := a) z‖ ≤ bound cap := by
  change ‖Real.sqrt (a z)‖ ≤ Real.sqrt cap
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (hb z).2

theorem error_nonneg (n : ℕ) : 0 ≤ error (C := C) (β := β) ell n := by
  exact mul_nonneg (mul_nonneg (CompatibleReference.rootConstant_nonneg ell) C.property)
    (Real.rpow_nonneg (CompactMollifier.radius_pos n).le _)

include hβ in
theorem error_tendsto : Tendsto (error (C := C) (β := β) ell) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ CompatibleReference.rootConstant ell*(C : ℝ)*CompactMollifier.radius n^(β : ℝ))
    atTop (𝓝 (0 : ℝ))
  simpa only [mul_zero] using
    (CompactMollifier.radius_tendsto.rpow_const_nhds_zero (show 0 < (β : ℝ) from hβ)).const_mul
      (CompatibleReference.rootConstant ell*C)

include ha hβ hell hb in
theorem close (n : ℕ) (z : ℝ) : ‖root (a := a) z-amplitude (a := a) n z‖ ≤ error (C := C) (β := β) ell n := by
  have hh := CompatibleReference.scalar_sqrt_lipschitz hell (hb z).1 (bounds ha hβ ell cap hell hb n z).1
  have hv := CompactMollifier.approximant_error (H := (C : ℝ)) (β := (β : ℝ))
    (ha.continuous hβ) C.property (show 0 ≤ (β : ℝ) from β.2)
    (fun x y ↦ by simpa only [Real.dist_eq] using ha.dist_le x y) n z
  rw [abs_sub_comm] at hv
  exact hh.trans ((mul_le_mul_of_nonneg_left hv (CompatibleReference.rootConstant_nonneg ell)).trans_eq
    (by change _ = CompatibleReference.rootConstant ell*(C : ℝ)*CompactMollifier.radius n^(β : ℝ); ring))

include ha hβ hell hb in
theorem square (n : ℕ) (z : ℝ) : variance (a := a) n z = amplitude (a := a) n z^2 :=
  (Real.sq_sqrt (hell.le.trans (bounds ha hβ ell cap hell hb n z).1)).symm

end SHEStochastic.PositiveScalarApproximation
