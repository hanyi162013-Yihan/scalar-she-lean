module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Nested finite time grids for an explicit Kolmogorov continuity
construction. The refinement base is an arbitrary natural B≥2. -/
noncomputable section
namespace SHE.DyadicClock
open Set Filter
open scoped Topology

def point (B n k : ℕ) : ℝ := (k:ℝ)/(B:ℝ)^n
def index (B n : ℕ) (t : ℝ) : ℕ := ⌊t*(B:ℝ)^n⌋₊
def approximate (B n : ℕ) (t : ℝ) : ℝ := point B n (index B n t)

variable {B : ℕ} (hB : 2 ≤ B)
include hB
theorem base_pos : 0 < B := by omega
theorem base_real_pos : (0:ℝ) < B := by exact_mod_cast base_pos hB

theorem point_mem {n k : ℕ} (hk : k ≤ B^n) : point B n k ∈ Icc (0:ℝ) 1 := by
  have hd : (0:ℝ) < (B:ℝ)^n := pow_pos (base_real_pos hB) n
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hd.le
  · rw [point,div_le_one hd]
    exact_mod_cast hk

theorem index_le {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : index B n t ≤ B^n := by
  have hp : 0 ≤ (B:ℝ)^n := (pow_pos (base_real_pos hB) n).le
  have he := Nat.floor_mono (mul_le_mul_of_nonneg_right ht.2 hp)
  simpa only [index,one_mul,← Nat.cast_pow,Nat.floor_natCast] using he

theorem approximate_mem {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    approximate B n t ∈ Icc (0:ℝ) 1 := point_mem hB (index_le hB ht)

theorem approximate_bounds {n : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    approximate B n t ≤ t ∧ t-approximate B n t < 1/(B:ℝ)^n := by
  have hd := pow_pos (base_real_pos hB) n
  have hx : 0 ≤ t*(B:ℝ)^n := mul_nonneg ht hd.le
  have hle := Nat.floor_le hx
  have hlt := Nat.lt_floor_add_one (t*(B:ℝ)^n)
  change (index B n t:ℝ) ≤ t*(B:ℝ)^n at hle
  change t*(B:ℝ)^n < (index B n t:ℝ)+1 at hlt
  constructor
  · exact (div_le_iff₀ hd).mpr hle
  · unfold approximate point
    apply (lt_div_iff₀ hd).mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    linarith

theorem approximate_tendsto {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => approximate B n t) atTop (𝓝 t) := by
  have hp : (1:ℝ) < B := by exact_mod_cast (by omega : 1 < B)
  have he : Tendsto (fun n => 1/(B:ℝ)^n) atTop (𝓝 (0:ℝ)) :=
    by simpa only [one_div,Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp)
  have hlow : Tendsto (fun n => t-1/(B:ℝ)^n) atTop (𝓝 t) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => by linarith [(approximate_bounds hB (n := n) ht).2])
    (fun n => (approximate_bounds hB ht).1)

theorem index_refine (n : ℕ) (t : ℝ) : index B (n+1) t/B=index B n t := by
  unfold index
  rw [pow_succ,← mul_assoc]
  exact Nat.mul_cast_floor_div_cancel (Nat.ne_of_gt (base_pos hB)) _

theorem refinement_bounds (n : ℕ) (t : ℝ) :
    B*index B n t ≤ index B (n+1) t ∧ index B (n+1) t < B*index B n t+B := by
  have he := Nat.mod_add_div (index B (n+1) t) B
  have hm := Nat.mod_lt (index B (n+1) t) (base_pos hB)
  rw [index_refine hB n t] at he
  omega

theorem point_refine (n k : ℕ) : point B n k=point B (n+1) (B*k) := by
  unfold point
  rw [pow_succ,Nat.cast_mul]
  field_simp [ne_of_gt (base_real_pos hB)]

end SHE.DyadicClock
