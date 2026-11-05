module

public import SHE.ContinuousPathRestriction
public import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.StoppedPathPasting
open Set MeasureTheory
open scoped NNReal

abbrev Time (H : ℝ≥0) := SHE.ContinuousPathRestriction.Interval H
abbrev Path (H : ℝ≥0) (E : Type*) [TopologicalSpace E] := C(Time H, E)

def origin (H : ℝ≥0) : Time H := ⟨0, le_rfl, H.property⟩

def pastTime (H : ℝ≥0) (r t : Time H) : Time H :=
  ⟨min t.val r.val, le_min t.property.1 r.property.1, (min_le_left _ _).trans t.property.2⟩

def futureTime (H : ℝ≥0) (r t : Time H) : Time H :=
  ⟨max (t.val - r.val) 0, le_max_right _ _, max_le
    ((sub_le_self _ r.property.1).trans t.property.2) H.property⟩

theorem continuous_pastTime (H : ℝ≥0) :
    Continuous (fun p : Time H × Time H ↦ pastTime H p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_snd).min
    (continuous_subtype_val.comp continuous_fst)).subtype_mk _

theorem continuous_futureTime (H : ℝ≥0) :
    Continuous (fun p : Time H × Time H ↦ futureTime H p.1 p.2) :=
  (((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).max continuous_const).subtype_mk _

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]

def stopped (H : ℝ≥0) (r : Time H) (x : Path H E) : Path H E :=
  x.comp ⟨pastTime H r, (continuous_pastTime H).comp (continuous_const.prodMk continuous_id)⟩

/-- Concatenation is continuous even on incompatible pairs. Subtracting
the future's initial value makes its increment zero at the join; under
the continuation kernel the matching initial state removes this shift. -/
def paste (H : ℝ≥0) (r : Time H) (x y : Path H E) : Path H E :=
  stopped H r x + y.comp ⟨futureTime H r,
    (continuous_futureTime H).comp (continuous_const.prodMk continuous_id)⟩ -
      ContinuousMap.const _ (y (origin H))

theorem paste_apply (H : ℝ≥0) (r t : Time H) (x y : Path H E) :
    paste H r x y t = x (pastTime H r t) + y (futureTime H r t) - y (origin H) := rfl

theorem paste_before (H : ℝ≥0) (r t : Time H) (x y : Path H E) (ht : t.val ≤ r.val) :
    paste H r x y t = x t := by
  have hp : pastTime H r t = t := Subtype.ext (min_eq_left ht)
  have hf : futureTime H r t = origin H := Subtype.ext (max_eq_right (sub_nonpos.mpr ht))
  rw [paste_apply, hp, hf, add_sub_cancel_right]

theorem paste_after (H : ℝ≥0) (r t : Time H) (x y : Path H E) (ht : r.val ≤ t.val)
    (hjoin : y (origin H) = x r) :
    paste H r x y t = y (futureTime H r t) := by
  have hp : pastTime H r t = r := Subtype.ext (min_eq_right ht)
  rw [paste_apply, hp, hjoin]
  abel

theorem stopped_paste (H : ℝ≥0) (r : Time H) (x y : Path H E) :
    stopped H r (paste H r x y) = stopped H r x := by
  ext t
  exact paste_before H r (pastTime H r t) x y (min_le_right _ _)

theorem paste_horizon (H : ℝ≥0) (x y : Path H E) :
    paste H ⟨H, H.property, le_rfl⟩ x y = x := by
  ext t
  exact paste_before H _ t x y t.property.2

theorem continuous_stopped (H : ℝ≥0) :
    Continuous (fun p : Time H × Path H E ↦ stopped H p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.snd.prodMk
    ((continuous_pastTime H).comp (continuous_fst.fst.prodMk continuous_snd)))

theorem continuous_paste (H : ℝ≥0) :
    Continuous (fun p : Time H × Path H E × Path H E ↦ paste H p.1 p.2.1 p.2.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_eval.comp (continuous_fst.snd.fst.prodMk
    ((continuous_pastTime H).comp (continuous_fst.fst.prodMk continuous_snd)))).add
    (continuous_eval.comp (continuous_fst.snd.snd.prodMk
      ((continuous_futureTime H).comp (continuous_fst.fst.prodMk continuous_snd))))).sub
        ((continuous_eval_const (origin H)).comp continuous_fst.snd.snd)

end SHEStochastic.StoppedPathPasting
