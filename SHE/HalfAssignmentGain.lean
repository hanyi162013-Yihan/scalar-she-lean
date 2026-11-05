module
public import SHE.AssignmentGapGain
public import SHE.AssignmentGapDegrees

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.AllocatedAssignmentKernel
open GaussianAssignmentBlocks AssignmentGapPartition Real
open scoped BigOperators
open Classical
variable {k : ℕ}

/-- Each nonempty rough block keeps one minimum gain. Its allocated
degrees sum to that gain; a root interval has its own quarter power. -/
def holderDegree (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (a : ℝ) (i : Fin k) : ℝ :=
  if label cs hc i=0 then 1/4 else a/((block cs (label cs hc i)).length:ℝ)

theorem holderDegree_pos_le_one (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) {a : ℝ}
    (ha : 0<a) (ha1 : a≤1) (i : Fin k) :
    0<holderDegree cs hc a i ∧ holderDegree cs hc a i≤1 := by
  by_cases hi : label cs hc i=0
  · simp only [holderDegree,hi,ite_true]
    norm_num
  · have h := degree_pos_le_one cs hc ha ha1 i
    simpa only [holderDegree,degree,hi,ite_false] using h

theorem gain_le_holder_product (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) {ν a : ℝ}
    (hν : 0≤ν) (ha : 0≤a) (d : Fin k→ℝ) (hd : ∀i,0≤d i) :
    gain cs ν a d≤(max 1 ν)^k*∏i,(d i)^(holderDegree cs hc a i) := by
  let C := max 1 ν
  have hC : 1≤C := le_max_left _ _
  have hb (l : Fin (k+1)) : gainBlock cs ν a d l≤
      ∏j : Fin (block cs l).length,
        C*(d ((block cs l).get j))^(if l=0 then (1/4:ℝ) else a/((block cs l).length:ℝ)) := by
    by_cases hl : l=0
    · simp only [gainBlock,hl,ite_true]
      apply Finset.prod_le_prod₀
      · intro j _
        exact le_min zero_le_one (mul_nonneg hν (Real.rpow_nonneg (hd _) _))
      · intro j _
        exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right
          (le_max_right 1 ν) (Real.rpow_nonneg (hd _) _))
    · simp only [gainBlock,hl,ite_false]
      split_ifs with he
      · have hempty : IsEmpty (Fin (block cs l).length) := by rw [he,List.length_nil];infer_instance
        letI := hempty
        simp
      · exact (MinimumGapAllocation.minimum_le_product (block cs l) he d
          (fun i _=>hd i) a ha).trans (Finset.prod_le_prod₀
            (fun j _=>Real.rpow_nonneg (hd _) _) (fun j _=>
              le_mul_of_one_le_left (Real.rpow_nonneg (hd _) _) hC))
  calc
    gain cs ν a d ≤ ∏l,∏j : Fin (block cs l).length,
        C*(d ((block cs l).get j))^(if l=0 then (1/4:ℝ) else a/((block cs l).length:ℝ)) :=
      Finset.prod_le_prod₀ (fun l _=>gainBlock_nonneg cs hν a d hd l) (fun l _=>hb l)
    _ = ∏i,C*(d i)^(holderDegree cs hc a i) := by
      convert! dependent_prod_blocks cs hc (fun l i=>
        C*(d i)^(if l=0 then (1/4:ℝ) else a/((block cs l).length:ℝ))) using 1
    _ = _ := by rw [Finset.prod_mul_distrib];simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,C]

/-- Half interpolation keeps half of each original block's total gain.
The root-frequency cost is allowed to depend on a fixed root cutoff. -/
theorem half_gain_bound (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) {ν a : ℝ}
    (hν : 0≤ν) (ha : 0≤a) (d : Fin k→ℝ) (hd : ∀i,0<d i) :
    (∏i,(d i)⁻¹)*sqrt (gain cs ν a d)≤
      (max 1 ν)^((k:ℝ)/2)*∏i,(d i)^(holderDegree cs hc a i/2-1) := by
  have hh := Real.sqrt_le_sqrt (gain_le_holder_product cs hc hν ha d (fun i=>(hd i).le))
  have hC : 0≤max 1 ν := zero_le_one.trans (le_max_left _ _)
  have he : sqrt ((max 1 ν)^k*∏i,(d i)^(holderDegree cs hc a i))=
      (max 1 ν)^((k:ℝ)/2)*∏i,(d i)^(holderDegree cs hc a i/2) := by
    rw [Real.sqrt_eq_rpow,Real.mul_rpow (pow_nonneg hC _) (Finset.prod_nonneg
      (fun i _=>Real.rpow_nonneg (hd i).le _)),←Real.finsetProd_rpow Finset.univ _
        (fun i _=>Real.rpow_nonneg (hd i).le _)]
    congr 1
    · rw [←Real.rpow_natCast,←Real.rpow_mul hC]
      congr 1
      ring
    · apply Finset.prod_congr rfl
      intro i _
      rw [←Real.rpow_mul (hd i).le]
      congr 1
      ring
  rw [he] at hh
  refine (mul_le_mul_of_nonneg_left hh (Finset.prod_nonneg (fun i _=>inv_nonneg.mpr (hd i).le))).trans_eq ?_
  rw [mul_left_comm,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [←Real.rpow_neg_one,←Real.rpow_add (hd i)]
  congr 1
  ring

end SHE.AllocatedAssignmentKernel
