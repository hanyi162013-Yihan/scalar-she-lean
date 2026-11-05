module

public import SHE.MinimumGapChoice
public import SHE.SharpWordTimeScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.MinimumGapAllocation
open Set MeasureTheory Real GaussianAssignmentBlocks
open scoped BigOperators
variable {ι : Type*}

/-- A minimum gain may be distributed over the original gaps of its
block. The degrees add to the full original exponent; no minimum is
replaced by a fixed chosen increment. -/
theorem minimum_le_product (is : List ι) (hne : is≠[]) (d : ι→ℝ)
    (hd : ∀ i∈is,0≤d i) (a : ℝ) (ha : 0≤a) :
    (d (MinimumGapChoice.choose d is hne))^a ≤
      ∏ j : Fin is.length,(d (is.get j))^(a/(is.length:ℝ)) := by
  let m := d (MinimumGapChoice.choose d is hne)
  have hm : 0≤m := hd _ (MinimumGapChoice.choose_mem d is hne)
  have hn : (0:ℝ) < is.length := by exact_mod_cast List.length_pos_iff_ne_nil.mpr hne
  have hp : 0≤a/(is.length:ℝ) := div_nonneg ha hn.le
  have he : (m^(a/(is.length:ℝ)))^is.length=m^a := by
    rw [←Real.rpow_mul_natCast hm]
    congr 1
    field_simp [ne_of_gt hn]
  calc
    _ = ∏ _j : Fin is.length,m^(a/(is.length:ℝ)) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,he]
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg hm _)
      intro j _
      exact Real.rpow_le_rpow hm
        (MinimumGapChoice.choose_le d is hne _ (List.get_mem is j)) hp

/-- The allocated degree is strictly positive for every member of a
nonempty block, and its sum is exactly the original Hölder gain. -/
theorem allocated_degrees (is : List ι) (hne : is≠[]) {a : ℝ} (ha : 0<a) :
    0<a/(is.length:ℝ) ∧
      (∑ _j : Fin is.length,a/(is.length:ℝ))=a := by
  have hn : (0:ℝ) < is.length := by exact_mod_cast List.length_pos_iff_ne_nil.mpr hne
  refine ⟨div_pos ha hn,?_⟩
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [ne_of_gt hn]

theorem blockChoice_le_product {r k : ℕ} (lo hi : Fin r→ℝ)
    (choices : List (Fin r×Fin k)) (factor : Fin k) (h : block choices factor≠[])
    (hgap : ∀ j∈block choices factor,lo j≤hi j) (a : ℝ) (ha : 0≤a) :
    (hi (MinimumGapChoice.blockChoice lo hi choices factor h)-
      lo (MinimumGapChoice.blockChoice lo hi choices factor h))^a ≤
      ∏ j : Fin (block choices factor).length,
        (hi ((block choices factor).get j)-lo ((block choices factor).get j))^
          (a/((block choices factor).length:ℝ)) :=
  minimum_le_product (block choices factor) h (fun j=>hi j-lo j)
    (fun j hj=>sub_nonneg.mpr (hgap j hj)) a ha

end SHE.MinimumGapAllocation
