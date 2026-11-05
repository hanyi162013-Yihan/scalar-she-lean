module

public import SHE.MinimumGapAllocation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.AssignmentGapPartition
open GaussianAssignmentBlocks
open scoped BigOperators
open Classical
variable {k m : ℕ}

theorem exists_label (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (i : Fin k) : ∃ l,(i,l)∈cs := by
  have hi : i∈cs.map Prod.fst := by rw [assignment_coordinates _ _ hc];simp
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hi
  refine ⟨p.2,?_⟩
  simpa only [←he,Prod.eta] using hp

def label (cs : List (Fin k×Fin m)) (hc : cs∈assignments (m:=m) (List.finRange k))
    (i : Fin k) : Fin m := Classical.choose (exists_label cs hc i)

theorem label_mem (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (i : Fin k) : (i,label cs hc i)∈cs :=
  Classical.choose_spec (exists_label cs hc i)

theorem coordinates_nodup (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) : (cs.map Prod.fst).Nodup := by
  rw [assignment_coordinates _ _ hc]
  exact List.nodup_finRange k

theorem mem_block_iff_label (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (i : Fin k) (l : Fin m) :
    i∈block cs l ↔ label cs hc i=l := by
  constructor
  · intro hi
    have he := List.inj_on_of_nodup_map (coordinates_nodup cs hc)
      (label_mem cs hc i) ((mem_block_iff cs l i).mp hi) (rfl : (i,label cs hc i).1=(i,l).1)
    exact congrArg Prod.snd he
  · intro hi
    rw [←hi]
    exact (mem_block_iff cs _ i).mpr (label_mem cs hc i)

theorem block_toFinset (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (l : Fin m) :
    (block cs l).toFinset=Finset.univ.filter (fun i=>label cs hc i=l) := by
  ext i
  simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,
    mem_block_iff_label cs hc]

theorem block_length (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (l : Fin m) :
    (Finset.univ.filter (fun i=>label cs hc i=l)).card=(block cs l).length := by
  rw [←block_toFinset]
  exact List.toFinset_card_of_nodup (block_nodup cs (coordinates_nodup cs hc) l)

theorem block_prod (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (l : Fin m) (f : Fin k→ℝ) :
    (∏ j : Fin (block cs l).length,f ((block cs l).get j))=
      ∏ i∈Finset.univ.filter (fun i=>label cs hc i=l),f i := by
  rw [←block_toFinset]
  have hh := List.prod_toFinset f (block_nodup cs (coordinates_nodup cs hc) l)
  rw [hh]
  simpa only [List.get_eq_getElem] using Fin.prod_univ_fun_getElem (block cs l) f

theorem block_sum (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (l : Fin m) (f : Fin k→ℝ) :
    (∑ j : Fin (block cs l).length,f ((block cs l).get j))=
      ∑ i∈Finset.univ.filter (fun i=>label cs hc i=l),f i := by
  rw [←block_toFinset]
  have hh := List.sum_toFinset f (block_nodup cs (coordinates_nodup cs hc) l)
  rw [hh]
  simpa only [List.get_eq_getElem] using Fin.sum_univ_fun_getElem (block cs l) f

/-- The actual finite assignment blocks partition every original gap
exactly once. This identity does not reorder or duplicate increments. -/
theorem prod_blocks (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (f : Fin k→ℝ) :
    (∏ l,∏ j : Fin (block cs l).length,f ((block cs l).get j))=∏ i,f i := by
  simp_rw [block_prod cs hc]
  exact Finset.prod_fiberwise Finset.univ (label cs hc) f

theorem sum_blocks (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (f : Fin k→ℝ) :
    (∑ l,∑ j : Fin (block cs l).length,f ((block cs l).get j))=∑ i,f i := by
  simp_rw [block_sum cs hc]
  exact Finset.sum_fiberwise Finset.univ (label cs hc) f

end SHE.AssignmentGapPartition
