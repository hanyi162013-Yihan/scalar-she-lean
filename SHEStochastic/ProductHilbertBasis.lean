module

public import SHE.OrthogonalItoChannels
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.ProductHilbertBasis
open SHE.OrthogonalItoChannels
open scoped Topology
variable {ι C : Type*} [DecidableEq ι] [NormedAddCommGroup C]
  [InnerProductSpace ℝ C] [CompleteSpace C]

def vectors (e : HilbertBasis ι ℝ C) : Sum ι ι → Both C :=
  Sum.elim (fun i ↦ left (e i)) (fun i ↦ right (e i))

theorem orthonormal (e : HilbertBasis ι ℝ C) : Orthonormal ℝ (vectors e) := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => simpa [vectors, (left (C := C)).inner_map_map] using
        (orthonormal_iff_ite.mp e.orthonormal i j)
    | inr j =>
        change inner ℝ (left (e i)) (right (e j)) = _
        simp [left, right, WithLp.prod_inner_apply]
  | inr i => cases j with
    | inl j =>
        change inner ℝ (right (e i)) (left (e j)) = _
        simp [left, right, WithLp.prod_inner_apply]
    | inr j => simpa [vectors, (right (C := C)).inner_map_map] using
        (orthonormal_iff_ite.mp e.orthonormal i j)

theorem total (e : HilbertBasis ι ℝ C) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (vectors e))).topologicalClosure := by
  let S := (Submodule.span ℝ (Set.range (vectors e))).topologicalClosure
  have hc : IsClosed (S : Set (Both C)) := Submodule.isClosed_topologicalClosure _
  have hchan (L : C →ₗᵢ[ℝ] Both C) (hL : ∀ i, L (e i) ∈ S) (x : C) : L x ∈ S := by
    apply hc.mem_of_tendsto (L.toContinuousLinearMap.hasSum (e.hasSum_repr x))
    exact Filter.Eventually.of_forall fun s ↦ Submodule.sum_mem S (fun i _ ↦ by
      rw [map_smul]
      exact S.smul_mem _ (hL i))
  intro x _
  have hl : left x.ofLp.1 ∈ S := hchan left
    (fun i ↦ by
      apply (Submodule.span ℝ (Set.range (vectors e))).le_topologicalClosure
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩) _
  have hr : right x.ofLp.2 ∈ S := hchan right
    (fun i ↦ by
      apply (Submodule.span ℝ (Set.range (vectors e))).le_topologicalClosure
      exact Submodule.subset_span ⟨Sum.inr i, rfl⟩) _
  have he : left x.ofLp.1 + right x.ofLp.2 = x := by
    apply WithLp.ofLp_injective
    ext <;> simp [left, right]
  exact he ▸ S.add_mem hl hr

def basis (e : HilbertBasis ι ℝ C) : HilbertBasis (Sum ι ι) ℝ (Both C) :=
  HilbertBasis.mk (orthonormal e) (total e)

@[simp] theorem basis_inl (e : HilbertBasis ι ℝ C) (i : ι) : basis e (Sum.inl i) = left (e i) := by
  simp [basis, HilbertBasis.coe_mk, vectors]

@[simp] theorem basis_inr (e : HilbertBasis ι ℝ C) (i : ι) : basis e (Sum.inr i) = right (e i) := by
  simp [basis, HilbertBasis.coe_mk, vectors]

end SHEStochastic.ProductHilbertBasis
