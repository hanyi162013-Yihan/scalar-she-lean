module

public import SHE.HaarConstantJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.FiniteOptionEnergy
open SHE.FiniteHaar
variable {d α : Type*} [Fintype d]

/-- Count every finite state component and every root/detail index
exactly once. This is shared by all vector column energy estimates. -/
theorem sum (F : d × Option α → ℝ) (hF : ∀ k, 0 ≤ F k)
    (hdetail : Summable (fun p => ∑ i : d, F (i, some p))) :
    Summable F ∧ (∑' k, F k) = (∑' p, ∑ i : d, F (i, some p)) + ∑ i : d, F (i, none) := by
  let G := fun q : Option α => ∑ i : d, F (i,q)
  have ho := option_energy_sum G hdetail
  have hqd : Summable (fun qi : Option α × d => F (qi.2,qi.1)) :=
    (summable_prod_of_nonneg (fun qi => hF _)).mpr
      ⟨fun q => (hasSum_fintype _).summable, by simpa only [tsum_fintype] using ho.1⟩
  refine ⟨hqd.prod_symm, ?_⟩
  calc
    _ = ∑' qi : Option α × d, F (qi.2,qi.1) := (Equiv.prodComm (Option α) d).tsum_eq F |>.symm
    _ = ∑' q, G q := by simpa only [G, tsum_fintype] using hqd.tsum_prod
    _ = _ := ho.2

end SHEStochastic.FiniteOptionEnergy
