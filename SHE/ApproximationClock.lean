module

public import SHE.CompactMollifier
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.ApproximationClock
open MeasureTheory Filter Set
open scoped Topology

abbrev delta := CompactMollifier.radius
def right (n : ℕ) (t : ℝ) : ℝ := delta n*(⌈t/delta n⌉₊:ℝ)
def left (n : ℕ) (t : ℝ) : ℝ := right n t-delta n

theorem delta_pos (n : ℕ) : 0 < delta n := CompactMollifier.radius_pos n
theorem delta_tendsto : Tendsto delta atTop (𝓝 (0:ℝ)) := CompactMollifier.radius_tendsto

theorem right_bounds (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : t ≤ right n t ∧ right n t < t+delta n := by
  have hd := delta_pos n
  constructor
  · have hh := (div_le_iff₀ hd).mp (Nat.le_ceil (t/delta n))
    simpa only [right,mul_comm] using hh
  · have hh := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (div_nonneg ht hd.le)) hd
    change delta n*(⌈t/delta n⌉₊:ℝ) < _
    convert hh using 1
    field_simp

theorem left_bounds (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ left n t ∧ left n t < t ∧ t-delta n ≤ left n t := by
  have hb := right_bounds n ht.le
  have hn : 1 ≤ ⌈t/delta n⌉₊ := Nat.one_le_ceil_iff.mpr (div_pos ht (delta_pos n))
  have hn' : (1:ℝ) ≤ (⌈t/delta n⌉₊:ℝ) := by exact_mod_cast hn
  have hl := mul_le_mul_of_nonneg_left hn' (delta_pos n).le
  change 0 ≤ right n t-delta n ∧ right n t-delta n < t ∧ t-delta n ≤ right n t-delta n
  change delta n*1 ≤ right n t at hl
  constructor
  · linarith
  · constructor <;> linarith

theorem right_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun n => right n t) atTop (𝓝 t) := by
  have hu : Tendsto (fun n => t+delta n) atTop (𝓝 t) := by
    simpa only [add_zero] using delta_tendsto.const_add t
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (right_bounds n ht).1) (fun n => (right_bounds n ht).2.le)

theorem left_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun n => left n t) atTop (𝓝 t) := by
  change Tendsto (fun n => right n t-delta n) atTop (𝓝 t)
  simpa only [sub_zero] using (right_tendsto ht).sub delta_tendsto

theorem right_measurable (n : ℕ) : Measurable (right n) := by
  unfold right
  fun_prop

theorem left_measurable (n : ℕ) : Measurable (left n) := (right_measurable n).sub_const _

end SHE.ApproximationClock
