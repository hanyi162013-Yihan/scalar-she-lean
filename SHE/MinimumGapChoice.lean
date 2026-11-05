module

public import SHE.ActualPointMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.MinimumGapChoice
open Set MeasureTheory Real GaussianAssignmentBlocks
variable {ι X : Type*} [MeasurableSpace X]

/-- Explicit finite minimum selection, with a deterministic tie rule. -/
def pick (f : ι→ℝ) (a : ι) : List ι→ι
  | [] => a
  | b::bs => let c := pick f b bs; if f a≤f c then a else c

theorem pick_mem (f : ι→ℝ) (a : ι) (is : List ι) : pick f a is∈a::is := by
  induction is generalizing a with
  | nil => simp only [pick,List.mem_singleton]
  | cons b bs ih =>
    simp only [pick]
    split_ifs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih b)

theorem pick_le (f : ι→ℝ) (a : ι) (is : List ι) (j : ι) (hj : j∈a::is) :
    f (pick f a is)≤f j := by
  induction is generalizing a with
  | nil =>
    obtain rfl := List.mem_singleton.mp hj
    exact le_rfl
  | cons b bs ih =>
    simp only [pick]
    split_ifs with h
    · rcases List.mem_cons.mp hj with rfl|hj
      · exact le_rfl
      · exact h.trans (ih b hj)
    · rcases List.mem_cons.mp hj with rfl|hj
      · exact (lt_of_not_ge h).le
      · exact ih b hj

theorem pick_value (f : ι→ℝ) (a b : ι) (bs : List ι) :
    f (pick f a (b::bs))=min (f a) (f (pick f b bs)) := by
  simp only [pick]
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (lt_of_not_ge h).le).symm

theorem pick_value_measurable (f : X→ι→ℝ) (hf : ∀ i,Measurable (fun x => f x i))
    (a : ι) (is : List ι) : Measurable (fun x => f x (pick (f x) a is)) := by
  induction is generalizing a with
  | nil => exact hf a
  | cons b bs ih =>
    simp_rw [pick_value]
    exact (hf a).min (ih b)

theorem pick_measurable [MeasurableSpace ι] (f : X→ι→ℝ)
    (hf : ∀ i,Measurable (fun x => f x i)) (a : ι) (is : List ι) :
    Measurable (fun x => pick (f x) a is) := by
  induction is generalizing a with
  | nil => exact measurable_const
  | cons b bs ih =>
    exact measurable_const.ite (measurableSet_le (hf a) (pick_value_measurable f hf b bs)) (ih b)

def choose (f : ι→ℝ) (is : List ι) (h : is≠[]) : ι :=
  match is with
  | [] => False.elim (h rfl)
  | a::as => pick f a as

theorem choose_mem (f : ι→ℝ) (is : List ι) (h : is≠[]) : choose f is h∈is := by
  cases is with
  | nil => exact False.elim (h rfl)
  | cons a as => exact pick_mem f a as

theorem choose_le (f : ι→ℝ) (is : List ι) (h : is≠[]) (j : ι) (hj : j∈is) :
    f (choose f is h)≤f j := by
  cases is with
  | nil => exact False.elim (h rfl)
  | cons a as => exact pick_le f a as j hj

theorem choose_measurable [MeasurableSpace ι] (f : X→ι→ℝ)
    (hf : ∀ i,Measurable (fun x => f x i)) (is : List ι) (h : is≠[]) :
    Measurable (fun x => choose (f x) is h) := by
  cases is with
  | nil => exact False.elim (h rfl)
  | cons a as => exact pick_measurable f hf a as

theorem choose_value_measurable (f : X→ι→ℝ) (hf : ∀ i,Measurable (fun x => f x i))
    (is : List ι) (h : is≠[]) : Measurable (fun x => f x (choose (f x) is h)) := by
  cases is with
  | nil => exact False.elim (h rfl)
  | cons a as => exact pick_value_measurable f hf a as

def blockChoice {r k : ℕ} (lo hi : Fin r→ℝ) (choices : List (Fin r×Fin k))
    (factor : Fin k) (h : block choices factor≠[]) : Fin r :=
  choose (fun j => hi j-lo j) (block choices factor) h

theorem blockChoice_mem {r k : ℕ} (lo hi : Fin r→ℝ) (choices : List (Fin r×Fin k))
    (factor : Fin k) (h : block choices factor≠[]) : blockChoice lo hi choices factor h∈block choices factor :=
  choose_mem _ _ _

/-- Every assigned old gap is retained simultaneously through the true
minimum, rather than a single fixed interval chosen before the times. -/
theorem blockChoice_gap_le {r k : ℕ} (lo hi : Fin r→ℝ) (choices : List (Fin r×Fin k))
    (factor : Fin k) (h : block choices factor≠[]) (j : Fin r) (hj : j∈block choices factor) :
    hi (blockChoice lo hi choices factor h)-lo (blockChoice lo hi choices factor h)≤hi j-lo j := by
  convert! choose_le (fun j => hi j-lo j) (block choices factor) h j hj using 1

theorem blockChoice_measurable {r k : ℕ} (lo hi : X→Fin r→ℝ)
    (hlo : ∀ j,Measurable (fun x => lo x j)) (hhi : ∀ j,Measurable (fun x => hi x j))
    (choices : List (Fin r×Fin k)) (factor : Fin k) (h : block choices factor≠[]) :
    Measurable (fun x => blockChoice (lo x) (hi x) choices factor h) :=
  choose_measurable _ (fun j => (hhi j).sub (hlo j)) _ h

theorem blockChoice_gap_measurable {r k : ℕ} (lo hi : X→Fin r→ℝ)
    (hlo : ∀ j,Measurable (fun x => lo x j)) (hhi : ∀ j,Measurable (fun x => hi x j))
    (choices : List (Fin r×Fin k)) (factor : Fin k) (h : block choices factor≠[]) :
    Measurable (fun x => hi x (blockChoice (lo x) (hi x) choices factor h)-
      lo x (blockChoice (lo x) (hi x) choices factor h)) :=
  choose_value_measurable _ (fun j => (hhi j).sub (hlo j)) _ h

end SHE.MinimumGapChoice
