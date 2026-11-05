module

public import SHEStochastic.AdaptedRestartGluing
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.CountablePathConcatenation
open MeasureTheory
open scoped NNReal
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

def finite (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) : ℕ → ℝ≥0 → E
  | 0,t => f 0 (min t H)
  | m+1,t => finite H f m (min t ((m+1 : ℕ) * H))+
      (f (m+1) (min (t-((m+1 : ℕ)*H)) H)-f (m+1) 0)

theorem finite_continuous (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) (hf : ∀ j,Continuous (f j)) :
    ∀ m,Continuous (finite H f m) := by
  intro m
  induction m with
  | zero => exact (hf 0).comp (continuous_id.min continuous_const)
  | succ m ih =>
    exact (ih.comp (continuous_id.min continuous_const)).add
      (((hf (m+1)).comp ((continuous_id.sub continuous_const).min continuous_const)).sub continuous_const)

theorem finite_before (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) (m : ℕ) (t : ℝ≥0)
    (ht : t≤(m+1 : ℕ)*H) : finite H f (m+1) t=finite H f m t := by
  change finite H f m (min t ((m+1 : ℕ)*H))+
    (f (m+1) (min (t-((m+1 : ℕ)*H)) H)-f (m+1) 0)=_
  rw [min_eq_left ht,tsub_eq_zero_of_le ht]
  simp

theorem finite_agree (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) {i j : ℕ} (hij : i≤j)
    (t : ℝ≥0) (ht : t≤(i+1 : ℕ)*H) : finite H f j t=finite H f i t := by
  induction j with
  | zero => have hi : i=0 := Nat.eq_zero_of_le_zero hij; subst i; rfl
  | succ j ih =>
    by_cases he : i=j+1
    · subst i; rfl
    · have hi : i≤j := by omega
      rw [finite_before H f j t (ht.trans (by gcongr)),ih hi]

/-- Anchored gluing makes every path continuous, even for exceptional
block sequences whose endpoint states fail to match. -/
def value (H : ℝ≥0) (f : ℕ → ℝ≥0 → E) (t : ℝ≥0) : E :=
  finite H f ⌈t/H⌉₊ t

theorem covering (H t : ℝ≥0) (hH : 0<H) : t≤(⌈t/H⌉₊+1 : ℕ)*H := by
  have h := Nat.le_ceil (t/H)
  have ht : t≤(⌈t/H⌉₊ : ℝ≥0)*H := (div_le_iff₀ hH).mp h
  exact ht.trans (by gcongr; exact_mod_cast Nat.le_succ ⌈t/H⌉₊)

theorem value_eq_finite (H : ℝ≥0) (hH : 0<H) (f : ℕ → ℝ≥0 → E)
    (m : ℕ) (t : ℝ≥0) (ht : t≤(m+1 : ℕ)*H) : value H f t=finite H f m t := by
  unfold value
  by_cases hm : m≤⌈t/H⌉₊
  · exact finite_agree H f hm t ht
  · exact (finite_agree H f (le_of_lt (lt_of_not_ge hm)) t (covering H t hH)).symm

theorem continuous (H : ℝ≥0) (hH : 0<H) (f : ℕ → ℝ≥0 → E)
    (hf : ∀ j,Continuous (f j)) : Continuous (value H f) := by
  rw [continuous_iff_continuousAt]
  intro t
  let m := ⌈t/H⌉₊+1
  have ht : t<(m+1 : ℕ)*H := lt_of_le_of_lt (covering H t hH) (by
    dsimp [m]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self (⌈t/H⌉₊+1)) hH)
  apply ((finite_continuous H f hf m).continuousAt).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact value_eq_finite H hH f m s hs.le

theorem block (H : ℝ≥0) (hH : 0<H) (f : ℕ → ℝ≥0 → E)
    (hMatch : ∀ j,f (j+1) 0=f j H) (j : ℕ) (s : ℝ≥0) (hs : s≤H) :
    value H f ((j : ℝ≥0)*H+s)=f j s := by
  rw [value_eq_finite H hH f j _ (by push_cast; nlinarith)]
  induction j generalizing s with
  | zero => simp [finite,min_eq_left hs]
  | succ j ih =>
    have hp : min (((j+1 : ℕ) : ℝ≥0)*H+s) (((j+1 : ℕ) : ℝ≥0)*H)=((j+1 : ℕ) : ℝ≥0)*H :=
      min_eq_right (le_add_of_nonneg_right (show (0 : ℝ≥0)≤s from bot_le))
    rw [finite,hp,add_tsub_cancel_left,min_eq_left hs]
    have hi : finite H f j (((j+1 : ℕ) : ℝ≥0)*H)=f j H := by
      convert ih H le_rfl using 1 <;> push_cast <;> ring
    rw [hi,←hMatch j]
    abel

/-- Every finite time belongs to an explicit local block. -/
theorem exists_block (H : ℝ≥0) (hH : 0<H) (t : ℝ≥0) :
    ∃ (j : ℕ) (s : ℝ≥0),s≤H ∧ (j : ℝ≥0)*H+s=t := by
  let j := ⌊t/H⌋₊
  have hleft : (j : ℝ≥0)*H≤t :=
    (le_div_iff₀ hH).mp (Nat.floor_le (show (0 : ℝ≥0)≤t/H from bot_le))
  have hright : t<(j+1 : ℕ)*H := by
    rw [←div_lt_iff₀ hH]
    simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (t/H)
  refine ⟨j,t-(j : ℝ≥0)*H,?_,add_tsub_cancel_of_le hleft⟩
  apply (tsub_le_iff_right).mpr
  calc
    t ≤ (j+1 : ℕ)*H := hright.le
    _ = H+(j : ℝ≥0)*H := by push_cast; ring

/-- Driver increments need no matching of absolute driver values;
each new local driver is anchored at its own time zero. -/
theorem increment (H : ℝ≥0) (hH : 0<H) (f : ℕ → ℝ≥0 → E)
    (j : ℕ) (s : ℝ≥0) (hs : s≤H) :
    value H f ((j : ℝ≥0)*H+s)-value H f ((j : ℝ≥0)*H)=f j s-f j 0 := by
  rw [value_eq_finite H hH f j _ (by push_cast; nlinarith),
    value_eq_finite H hH f j _ (by gcongr; exact_mod_cast Nat.le_succ j)]
  cases j with
  | zero => simp [finite,min_eq_left hs]
  | succ j =>
    change (finite H f j (min (((j+1 : ℕ) : ℝ≥0)*H+s) (((j+1 : ℕ) : ℝ≥0)*H))+
      (f (j+1) (min ((((j+1 : ℕ) : ℝ≥0)*H+s)-((j+1 : ℕ) : ℝ≥0)*H) H)-f (j+1) 0))-
      (finite H f j (min (((j+1 : ℕ) : ℝ≥0)*H) (((j+1 : ℕ) : ℝ≥0)*H))+
        (f (j+1) (min ((((j+1 : ℕ) : ℝ≥0)*H)-((j+1 : ℕ) : ℝ≥0)*H) H)-f (j+1) 0))=_
    rw [min_eq_right (le_add_of_nonneg_right (show (0 : ℝ≥0)≤s from bot_le)),
      min_self,add_tsub_cancel_left,tsub_self,min_eq_left hs]
    simp

section Measurable
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem finite_measurable (H : ℝ≥0) (f : ℕ → ℝ≥0×Ω → E) (hf : ∀ j,Measurable (f j)) :
    ∀ m,Measurable (fun p : ℝ≥0×Ω => finite H (fun j t => f j (t,p.2)) m p.1) := by
  intro m
  induction m with
  | zero => exact (hf 0).comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  | succ m ih =>
    exact (ih.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)).add
      (((hf (m+1)).comp (((measurable_fst.sub measurable_const).min measurable_const).prodMk measurable_snd)).sub
        ((hf (m+1)).comp (measurable_const.prodMk measurable_snd)))

theorem measurable (H : ℝ≥0) (f : ℕ → ℝ≥0×Ω → E) (hf : ∀ j,Measurable (f j)) :
    Measurable (fun p : ℝ≥0×Ω => value H (fun j t => f j (t,p.2)) p.1) := by
  have hm : Measurable (fun q : (ℝ≥0×Ω)×ℕ => finite H (fun j t => f j (t,q.1.2)) q.2 q.1.1) :=
    measurable_from_prod_countable_left (finite_measurable H f hf)
  exact hm.comp (measurable_id.prodMk (Nat.measurable_ceil.comp (measurable_fst.div_const H)))

end Measurable

end SHEStochastic.CountablePathConcatenation
