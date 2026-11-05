module

public import SHE.HaarHigherHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.DyadicGenerationEnergy
open SHE.FiniteHaar

/-- Reindex an actual nonnegative dyadic packet family by generation,
using the already proved path/grid bijection. -/
theorem sum (F : List Bool → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hg : Summable (fun n => ∑ x : Grid n, F (leafPath n x))) :
    Summable F ∧ (∑' p, F p) = ∑' n, ∑ x : Grid n, F (leafPath n x) := by
  have hsig : Summable (fun nx : Σ n, Grid n => F (leafPath nx.1 nx.2)) := by
    apply (summable_sigma_of_nonneg (fun nx => hF _)).mpr
    exact ⟨fun n => (hasSum_fintype _).summable, by simpa only [tsum_fintype] using hg⟩
  refine ⟨generationPathEquiv.summable_iff.mp hsig, ?_⟩
  rw [← generationPathEquiv.tsum_eq F]
  simpa only [generationPathEquiv, Equiv.ofBijective_apply, tsum_fintype] using hsig.tsum_sigma

end SHEStochastic.DyadicGenerationEnergy
