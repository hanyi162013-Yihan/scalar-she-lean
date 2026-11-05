module

public import SHE.AssignedSimplexIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.MinimumGapChoice
open Classical
variable {α β : Type*}

theorem pick_map (f : β→ℝ) (e : α→β) (a : α) (is : List α) :
    pick f (e a) (is.map e)=e (pick (fun i=>f (e i)) a is) := by
  induction is generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,pick,ih]
    split_ifs <;> rfl

theorem choose_map (f : β→ℝ) (e : α→β) (is : List α) (h : is≠[]) (he : is.map e≠[]) :
    choose f (is.map e) he=e (choose (fun i=>f (e i)) is h) := by
  cases is with
  | nil => exact False.elim (h rfl)
  | cons a as => exact pick_map f e a as

end SHE.MinimumGapChoice

namespace SHE.AllocatedAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
open scoped BigOperators
open Classical
variable {k m : ℕ}

def gainBlock (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) (l : Fin (m+1)) : ℝ :=
  if l=0 then ∏ j : Fin (block cs l).length,min 1 (ν*(d ((block cs l).get j))^(1/4:ℝ))
  else if h : block cs l=[] then 1 else (d (MinimumGapChoice.choose d (block cs l) h))^a

def gain (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) : ℝ := ∏ l,gainBlock cs ν a d l

def emptyGain (cs : List (Fin k×Fin (m+1))) (a : ℝ) (age : Fin m→ℝ) : ℝ :=
  ∏ j,if block cs j.succ=[] then (age j)^a else 1

theorem gainBlock_nonneg (cs : List (Fin k×Fin (m+1))) {ν : ℝ} (hν : 0≤ν)
    (a : ℝ) (d : Fin k→ℝ) (hd : ∀ i,0≤d i) (l : Fin (m+1)) : 0≤gainBlock cs ν a d l := by
  unfold gainBlock
  split_ifs
  · exact Finset.prod_nonneg (fun j _=>le_min zero_le_one
      (mul_nonneg hν (Real.rpow_nonneg (hd _) _)))
  · exact zero_le_one
  · exact Real.rpow_nonneg (hd _) _

theorem blockWeight_eq (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) (l : Fin (m+1)) :
    blockWeight cs ν a d l=
      (∏ j : Fin (block cs l).length,(d ((block cs l).get j))⁻¹)*gainBlock cs ν a d l := by
  unfold blockWeight gainBlock
  split_ifs with hl hb
  · rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    simp only [rootKernel,Real.rpow_neg_one]
  · have hempty : IsEmpty (Fin (block cs l).length) := by rw [hb,List.length_nil];infer_instance
    letI := hempty
    simp
  · rfl

theorem inverse_mul_gain_eq_weight (cs : List (Fin k×Fin (m+1)))
    (hc : cs∈assignments (m:=m+1) (List.finRange k)) (ν a : ℝ) (d : Fin k→ℝ) :
    (∏ i,(d i)⁻¹)*gain cs ν a d=weight cs ν a d := by
  rw [←prod_blocks cs hc (fun i=>(d i)⁻¹)]
  unfold gain weight
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  exact (blockWeight_eq cs ν a d l).symm

theorem gain_eq_root_rough (cs : List (Fin k×Fin (m+1))) (ν a : ℝ) (d : Fin k→ℝ) :
    gain cs ν a d=
      (∏ j : Fin (block cs 0).length,min 1 (ν*(d ((block cs 0).get j))^(1/4:ℝ)))*
      ∏ l : Fin m,if h : block cs l.succ=[] then 1 else (d (MinimumGapChoice.choose d (block cs l.succ) h))^a := by
  rw [gain,Fin.prod_univ_succ]
  simp only [gainBlock,ite_true,Fin.succ_ne_zero,ite_false]

theorem emptyGain_bound (cs : List (Fin k×Fin (m+1))) {a T : ℝ} (ha : 0≤a) (hT : 0≤T)
    (age : Fin m→ℝ) (hage : ∀ j,0≤age j ∧ age j≤T) :
    emptyGain cs a age≤T^(a*((Finset.univ.filter (fun j : Fin m=>block cs j.succ=[])).card:ℝ)) := by
  unfold emptyGain
  have hh : (∏ j : Fin m,if block cs j.succ=[] then (age j)^a else 1)≤
      ∏ j : Fin m,if block cs j.succ=[] then T^a else 1 := by
    apply Finset.prod_le_prod₀
    · intro j _
      split_ifs
      · exact Real.rpow_nonneg (hage j).1 _
      · exact zero_le_one
    · intro j _
      split_ifs
      · exact Real.rpow_le_rpow (hage j).1 (hage j).2 ha
      · exact le_rfl
  refine hh.trans_eq ?_
  rw [←Finset.prod_filter]
  simp only [Finset.prod_const]
  rw [←Real.rpow_mul_natCast hT]

end SHE.AllocatedAssignmentKernel
