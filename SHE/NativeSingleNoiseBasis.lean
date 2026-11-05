module
public import SHE.NativeNoiseHilbertBasis
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeSingleNoiseBasis
open FiniteHaar
theorem total : (Submodule.span ℝ (Set.range NativeTwoChannelNoiseBasis.haar))ᗮ=⊥ := by
  apply le_antisymm
  · intro x hx
    have hi (i:HaarNode) : inner ℝ (NativeTwoChannelNoiseBasis.haar i) x=0 :=
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨i,rfl⟩)
    change x=0
    apply lp.ext
    funext i
    simpa [NativeTwoChannelNoiseBasis.haar,lp.inner_single_left] using hi i
  · exact bot_le

def basis : HilbertBasis HaarNode ℝ RealHaarInput :=
  HilbertBasis.mkOfOrthogonalEqBot NativeTwoChannelNoiseBasis.haar_orthonormal total

@[simp] theorem basis_apply (i:HaarNode) : basis i=lp.single 2 i (1:ℝ) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot NativeTwoChannelNoiseBasis.haar_orthonormal total) i
end SHE.NativeSingleNoiseBasis
