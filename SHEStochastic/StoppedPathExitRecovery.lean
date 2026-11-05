module

public import SHEStochastic.StoppedPathPasting
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.StoppedPathExitRecovery
open Set MeasureTheory StoppedPathPasting
open scoped NNReal

local instance (H : ℝ≥0) : Fact ((0 : ℝ) ≤ H) := ⟨H.property⟩

variable {E : Type*} [NormedAddCommGroup E] (H : ℝ≥0) (a : E → ℝ) (R : ℝ)

/-- The closed-level exit clipped to the horizon. Empty hitting sets
are assigned the endpoint H explicitly. -/
def time (x : Path H E) : Time H := by
  classical
  exact if h : {t : Time H | R ≤ a (x t)}.Nonempty then sInf {t : Time H | R ≤ a (x t)} else ⊤

theorem time_le_of_hit (x : Path H E) (t : Time H) (ht : R ≤ a (x t)) :
    time H a R x ≤ t := by
  rw [time, dif_pos (show {s : Time H | R ≤ a (x s)}.Nonempty from ⟨t, ht⟩)]
  exact csInf_le (OrderBot.bddBelow _) ht

theorem before (x : Path H E) (t : Time H) (ht : t < time H a R x) : a (x t) < R := by
  by_contra h
  exact (not_le_of_gt ht) (time_le_of_hit H a R x t (le_of_not_gt h))

theorem attained (x : Path H E) (hc : IsClosed {t : Time H | R ≤ a (x t)})
    (hx : time H a R x ≠ ⊤) : R ≤ a (x (time H a R x)) := by
  have hn : {t : Time H | R ≤ a (x t)}.Nonempty := by
    by_contra hn
    apply hx
    exact dif_neg hn
  rw [time, dif_pos hn]
  exact hc.csInf_mem hn (OrderBot.bddBelow _)

/-- The closed exit state stays below the level, including a terminal
exit with no hit. This also covers a degenerate horizon or zero exit. -/
theorem at_exit_le (x : Path H E) (hc : Continuous (fun t ↦ a (x t)))
    (h0 : a (x (origin H)) ≤ R) : a (x (time H a R x)) ≤ R := by
  by_contra h
  have hb : a (x (⊥ : Time H)) ≤ R := h0
  obtain ⟨s, hs, he⟩ := intermediate_value_Ico
    (show (⊥ : Time H) ≤ time H a R x from bot_le) hc.continuousOn
    (show R ∈ Ico (a (x (⊥ : Time H))) (a (x (time H a R x))) from ⟨hb, lt_of_not_ge h⟩)
  exact (not_le_of_gt hs.2) (time_le_of_hit H a R x s he.ge)

/-- A continuous observable starting below the level hits that level
exactly at its first nonterminal exit. -/
theorem attained_eq (x : Path H E) (hc : Continuous (fun t ↦ a (x t)))
    (h0 : a (x (origin H)) ≤ R) (hx : time H a R x ≠ ⊤) :
    a (x (time H a R x)) = R :=
  le_antisymm (at_exit_le H a R x hc h0)
    (attained H a R x (isClosed_le continuous_const hc) hx)

theorem positive (x : Path H E) (hc : Continuous (fun t ↦ a (x t)))
    (hH : 0 < H) (h0 : a (x (origin H)) < R) : origin H < time H a R x := by
  by_contra h
  have he : time H a R x = origin H := le_antisymm (le_of_not_gt h) bot_le
  have hx : time H a R x ≠ ⊤ := by
    rw [he]
    intro hh
    have hv := congrArg Subtype.val hh
    change (0 : ℝ) = H at hv
    exact (ne_of_gt (show (0 : ℝ) < H from hH)) hv.symm
  have hh := attained H a R x (isClosed_le continuous_const hc) hx
  rw [he] at hh
  exact (not_le_of_gt h0) hh

theorem time_le_iff_of_lt_top (x : Path H E)
    (hc : IsClosed {s : Time H | R ≤ a (x s)}) (t : Time H) (ht : t < ⊤) :
    time H a R x ≤ t ↔ ∃ s : Time H, s ≤ t ∧ R ≤ a (x s) := by
  constructor
  · intro h
    exact ⟨time H a R x, h, attained H a R x hc (ne_of_lt (h.trans_lt ht))⟩
  · rintro ⟨s, hs, hh⟩
    exact (time_le_of_hit H a R x s hh).trans hs

/-- Retaining the closed hitting state at the join recovers exactly
the same exit time from the pasted path, regardless of the future. -/
theorem time_paste (x y : Path H E)
    (hhit : time H a R x ≠ ⊤ → R ≤ a (x (time H a R x))) :
    time H a R (paste H (time H a R x) x y) = time H a R x := by
  apply le_antisymm
  · by_cases hx : time H a R x = ⊤
    · rw [hx]; exact le_top
    · apply time_le_of_hit
      rw [paste_before H _ _ _ _ le_rfl]
      exact hhit hx
  · by_cases hn : {t : Time H | R ≤ a (paste H (time H a R x) x y t)}.Nonempty
    · conv_rhs => rw [time, dif_pos hn]
      apply le_csInf hn
      intro t ht
      apply le_of_not_gt
      intro hlt
      have hp := paste_before H (time H a R x) t x y hlt.le
      exact (not_le_of_gt (before H a R x t hlt)) (hp ▸ ht)
    · conv_rhs => rw [time, dif_neg hn]
      exact le_top

def stoppedPath (x : Path H E) : Path H E := stopped H (time H a R x) x

theorem prefix_paste (x y : Path H E)
    (hhit : time H a R x ≠ ⊤ → R ≤ a (x (time H a R x))) :
    stoppedPath H a R (paste H (time H a R x) x y) = stoppedPath H a R x := by
  dsimp [stoppedPath]
  rw [time_paste H a R x y hhit]
  exact stopped_paste H (time H a R x) x y

include a in
theorem measurable_time (ha : Continuous a) : Measurable (time H a R) := by
  apply measurable_of_Iic
  intro t
  by_cases ht : t = ⊤
  · simp only [ht, Set.preimage, mem_Iic, le_top, setOf_true]
    exact MeasurableSet.univ
  · let C : Set (Path H E × Time H) := {p | p.2 ≤ t ∧ R ≤ a (p.1 p.2)}
    have hC : IsClosed C := (isClosed_le continuous_snd continuous_const).inter
      (isClosed_le continuous_const (ha.comp continuous_eval))
    have he : (time H a R) ⁻¹' Iic t = Prod.fst '' C := by
      ext x
      constructor
      · intro hx
        have hx' : time H a R x ≤ t := hx
        have hne : time H a R x ≠ ⊤ := fun h ↦ ht (top_le_iff.mp (h ▸ hx'))
        exact ⟨(x, time H a R x), ⟨hx,
          attained H a R x (isClosed_le continuous_const (ha.comp x.continuous)) hne⟩, rfl⟩
      · rintro ⟨⟨y, s⟩, hs, rfl⟩
        change time H a R y ≤ t
        have hys : time H a R y ≤ s := time_le_of_hit H a R y s hs.2
        exact hys.trans hs.1
    rw [he]
    exact (isClosedMap_fst_of_compactSpace C hC).measurableSet

theorem measurable_prefix (ha : Continuous a) : Measurable (stoppedPath H a R) :=
  (continuous_stopped H).measurable.comp ((measurable_time H a R ha).prodMk measurable_id)

end SHEStochastic.StoppedPathExitRecovery
