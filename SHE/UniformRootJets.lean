module

public import SHE.UniformSmooth

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.UniformSmooth.UniformBoundedSmooth
open scoped BigOperators
variable {X E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A finite list of genuine uniform smoothness bounds admits one
finite jet constant, with frequency parameter one. -/
theorem finite_jet_bound {F : X→E→G} (hF : UniformBoundedSmooth F) (k : ℕ) :
    ∃ A : ℝ,0≤A ∧ ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A*(1:ℝ)^j := by
  choose M hM0 hM using hF.bounds
  refine ⟨∑ j∈Finset.range (k+1),M j,Finset.sum_nonneg (fun j _=>hM0 j),?_⟩
  intro x j hj z
  simpa only [one_pow,mul_one] using (hM j x z).trans
    (Finset.single_le_sum (fun i _=>hM0 i) (Finset.mem_range.mpr (by omega)))
end SHE.UniformSmooth.UniformBoundedSmooth
