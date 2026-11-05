module

public import SHE.AssignmentGapPartition
public import SHE.RootPowerGapKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.AssignmentGapPartition
open Set MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators
open Classical
variable {k m : ℕ}

theorem dependent_prod_blocks (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (f : Fin m→Fin k→ℝ) :
    (∏ l,∏ j : Fin (block cs l).length,f l ((block cs l).get j))=
      ∏ i,f (label cs hc i) i := by
  simp_rw [block_prod cs hc]
  calc
    _ = ∏ l,∏ i∈Finset.univ.filter (fun i=>label cs hc i=l),f (label cs hc i) i := by
      apply Finset.prod_congr rfl
      intro l _
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_fiberwise Finset.univ (label cs hc) _

theorem dependent_sum_blocks (cs : List (Fin k×Fin m))
    (hc : cs∈assignments (m:=m) (List.finRange k)) (f : Fin m→Fin k→ℝ) :
    (∑ l,∑ j : Fin (block cs l).length,f l ((block cs l).get j))=
      ∑ i,f (label cs hc i) i := by
  simp_rw [block_sum cs hc]
  calc
    _ = ∑ l,∑ i∈Finset.univ.filter (fun i=>label cs hc i=l),f (label cs hc i) i := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ (label cs hc) _

end SHE.AssignmentGapPartition

namespace SHE.AllocatedAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
open scoped BigOperators
open Classical
variable {k m : ℕ}

def rootFlag (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) (i : Fin k) : Bool := decide (label cs hc i=0)

def degree (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) (a : ℝ) (i : Fin k) : ℝ :=
  if label cs hc i=0 then 1 else a/((block cs (label cs hc i)).length:ℝ)

def blockWeight (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) (l : Fin (m+1)) : ℝ :=
  if l=0 then ∏ j : Fin (block cs l).length,rootKernel ν (d ((block cs l).get j))
  else if h : block cs l=[] then 1 else
    (∏ j : Fin (block cs l).length,(d ((block cs l).get j))⁻¹)*
      (d (MinimumGapChoice.choose d (block cs l) h))^a

def weight (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) : ℝ :=
  ∏ l,blockWeight cs ν a d l

theorem blockWeight_nonneg (cs : List (Fin k×Fin (m+1))) {ν a : ℝ} (hν : 0≤ν)
    (d : Fin k→ℝ) (hd : ∀ i,0<d i) (l : Fin (m+1)) : 0≤blockWeight cs ν a d l := by
  unfold blockWeight
  split_ifs with hl hb
  · exact Finset.prod_nonneg (fun j _=>rootKernel_nonneg hν (hd _).le)
  · exact zero_le_one
  · exact mul_nonneg (Finset.prod_nonneg (fun j _=>inv_nonneg.mpr (hd _).le))
      (Real.rpow_nonneg (hd _).le _)

theorem degree_pos_le_one (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) {a : ℝ} (ha : 0<a) (ha1 : a≤1) (i : Fin k) :
    0<degree cs hc a i ∧ degree cs hc a i≤1 := by
  unfold degree
  split_ifs with h
  · exact ⟨zero_lt_one,le_rfl⟩
  · have hb : block cs (label cs hc i)≠[] := by
      intro he
      have hm := (mem_block_iff_label cs hc i (label cs hc i)).mpr rfl
      simpa only [he,List.not_mem_nil] using hm
    have hn : (0:ℝ) < (block cs (label cs hc i)).length := by
      exact_mod_cast List.length_pos_iff_ne_nil.mpr hb
    have hn1 : (1:ℝ)≤(block cs (label cs hc i)).length := by exact_mod_cast hn
    exact ⟨div_pos ha hn,(div_le_iff₀ hn).mpr (by nlinarith)⟩

/-- The literal minimum-weighted assignment is bounded by kernels on
the same original gaps, with no root clip lost. -/
theorem weight_le_allocated (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) {ν a : ℝ} (hν : 0≤ν) (ha : 0≤a)
    (d : Fin k→ℝ) (hd : ∀ i,0<d i) :
    weight cs ν a d≤∏ i,RootPowerGapKernels.kernel ν (degree cs hc a i) (rootFlag cs hc i) (d i) := by
  have hblock (l : Fin (m+1)) : blockWeight cs ν a d l≤
      ∏ j : Fin (block cs l).length,
        if l=0 then rootKernel ν (d ((block cs l).get j))
        else (d ((block cs l).get j))^(a/((block cs l).length:ℝ)-1) := by
    by_cases hl : l=0
    · simp only [blockWeight,hl,ite_true]
      exact le_rfl
    · simp only [blockWeight,hl,ite_false]
      split_ifs with hb
      · have hempty : IsEmpty (Fin (block cs l).length) := by
          rw [hb,List.length_nil]
          infer_instance
        letI := hempty
        simp
      · have hh := MinimumGapAllocation.minimum_le_product (block cs l) hb d
          (fun i _=>(hd i).le) a ha
        calc
          _ ≤ (∏ j : Fin (block cs l).length,(d ((block cs l).get j))⁻¹)*
              (∏ j : Fin (block cs l).length,(d ((block cs l).get j))^(a/((block cs l).length:ℝ))) :=
            mul_le_mul_of_nonneg_left hh (Finset.prod_nonneg (fun j _=>inv_nonneg.mpr (hd _).le))
          _ = _ := by
            rw [←Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro j _
            rw [←Real.rpow_neg_one,←Real.rpow_add (hd _)]
            congr 1
            ring
  calc
    _ ≤ ∏ l,∏ j : Fin (block cs l).length,
        if l=0 then rootKernel ν (d ((block cs l).get j))
        else (d ((block cs l).get j))^(a/((block cs l).length:ℝ)-1) := by
      exact Finset.prod_le_prod₀ (fun l _=>blockWeight_nonneg cs hν d hd l) (fun l _=>hblock l)
    _ = ∏ i,if label cs hc i=0 then rootKernel ν (d i)
        else (d i)^(a/((block cs (label cs hc i)).length:ℝ)-1) :=
      by
        convert! dependent_prod_blocks cs hc (fun l i=>
          if l=0 then rootKernel ν (d i) else (d i)^(a/((block cs l).length:ℝ)-1)) using 1
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : label cs hc i=0 <;>
        simp only [RootPowerGapKernels.kernel,degree,rootFlag,hi,decide_true,decide_false,
          Bool.false_eq_true,ite_true,ite_false]

end SHE.AllocatedAssignmentKernel
