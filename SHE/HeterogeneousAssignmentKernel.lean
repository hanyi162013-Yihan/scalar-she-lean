module

public import SHE.AssignmentGapDegrees
public import SHE.RootPowerGapKernels

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.HeterogeneousAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
open scoped BigOperators
open Classical
variable {k : ℕ}

def rootFlag (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (i : Fin k) : Bool := decide (label cs hc i=0)

def degree (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (a : Fin (k+1)→ℝ) (i : Fin k) : ℝ :=
  if label cs hc i=0 then 1 else a (label cs hc i)/((block cs (label cs hc i)).length:ℝ)

def blockWeight (cs : List (Fin k×Fin (k+1))) (ν : ℝ) (a : Fin (k+1)→ℝ) (d : Fin k→ℝ) (l : Fin (k+1)) : ℝ :=
  if l=0 then ∏ j : Fin (block cs l).length,rootKernel ν (d ((block cs l).get j))
  else if h : block cs l=[] then 1 else
    (∏ j : Fin (block cs l).length,(d ((block cs l).get j))⁻¹)*
      (d (MinimumGapChoice.choose d (block cs l) h))^(a l)

def weight (cs : List (Fin k×Fin (k+1))) (ν : ℝ) (a : Fin (k+1)→ℝ) (d : Fin k→ℝ) : ℝ :=
  ∏ l,blockWeight cs ν a d l

theorem blockWeight_nonneg (cs : List (Fin k×Fin (k+1))) {ν : ℝ} {a : Fin (k+1)→ℝ} (hν : 0≤ν)
    (d : Fin k→ℝ) (hd : ∀ i,0<d i) (l : Fin (k+1)) : 0≤blockWeight cs ν a d l := by
  unfold blockWeight
  split_ifs with hl hb
  · exact Finset.prod_nonneg (fun j _=>rootKernel_nonneg hν (hd _).le)
  · exact zero_le_one
  · exact mul_nonneg (Finset.prod_nonneg (fun j _=>inv_nonneg.mpr (hd _).le))
      (Real.rpow_nonneg (hd _).le _)

theorem degree_pos_le_one (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) {a : Fin (k+1)→ℝ} (ha : ∀ l,l≠0→0<a l) (ha1 : ∀ l,l≠0→a l≤1) (i : Fin k) :
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
    exact ⟨div_pos (ha _ h) hn,(div_le_iff₀ hn).mpr (by nlinarith [ha1 _ h])⟩

/-- The literal minimum-weighted assignment is bounded by kernels on
the same original gaps, with no root clip lost. -/
theorem weight_le_allocated (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) {ν : ℝ} {a : Fin (k+1)→ℝ} (hν : 0≤ν) (ha : ∀ l,l≠0→0≤a l)
    (d : Fin k→ℝ) (hd : ∀ i,0<d i) :
    weight cs ν a d≤∏ i,RootPowerGapKernels.kernel ν (degree cs hc a i) (rootFlag cs hc i) (d i) := by
  have hblock (l : Fin (k+1)) : blockWeight cs ν a d l≤
      ∏ j : Fin (block cs l).length,
        if l=0 then rootKernel ν (d ((block cs l).get j))
        else (d ((block cs l).get j))^((a l)/((block cs l).length:ℝ)-1) := by
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
          (fun i _=>(hd i).le) (a l) (ha l hl)
        calc
          _ ≤ (∏ j : Fin (block cs l).length,(d ((block cs l).get j))⁻¹)*
              (∏ j : Fin (block cs l).length,(d ((block cs l).get j))^((a l)/((block cs l).length:ℝ))) :=
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
        else (d ((block cs l).get j))^((a l)/((block cs l).length:ℝ)-1) := by
      exact Finset.prod_le_prod₀ (fun l _=>blockWeight_nonneg cs hν d hd l) (fun l _=>hblock l)
    _ = ∏ i,if label cs hc i=0 then rootKernel ν (d i)
        else (d i)^((a (label cs hc i))/((block cs (label cs hc i)).length:ℝ)-1) :=
      by
        convert! dependent_prod_blocks cs hc (fun l i=>
          if l=0 then rootKernel ν (d i) else (d i)^((a l)/((block cs l).length:ℝ)-1)) using 1
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : label cs hc i=0 <;>
        simp only [RootPowerGapKernels.kernel,degree,rootFlag,hi,decide_true,decide_false,
          Bool.false_eq_true,ite_true,ite_false]

end SHE.HeterogeneousAssignmentKernel
