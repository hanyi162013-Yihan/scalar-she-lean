module
public import SHE.NativeTwoChannelNoiseBasis
public import Mathlib.Analysis.InnerProductSpace.l2Space
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.NativeTwoChannelNoiseBasis
open FiniteHaar OrthogonalItoChannels

/-- The actual two-channel Haar columns are TOTAL in the original noise
space, not merely a partial orthonormal family. -/
theorem both_total:(Submodule.span ℝ (Set.range both))ᗮ=⊥:=by
  apply le_antisymm
  · intro x hx
    have hi(p:Bool×HaarNode):inner ℝ (both p) x=0:=
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨p,rfl⟩)
    have hl(i:HaarNode):((WithLp.ofLp x).1 i)=0:=by
      simpa[both,left,haar,WithLp.prod_inner_apply,lp.inner_single_left] using hi (true,i)
    have hr(i:HaarNode):((WithLp.ofLp x).2 i)=0:=by
      simpa[both,right,haar,WithLp.prod_inner_apply,lp.inner_single_left] using hi (false,i)
    change x=0
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply lp.ext
      funext i
      simpa using hl i
    · apply lp.ext
      funext i
      simpa using hr i
  · exact bot_le

/-- Genuine native noise Hilbert basis with the exact old Haar columns. -/
def basis:HilbertBasis (Bool×HaarNode) ℝ (Both RealHaarInput):=
  HilbertBasis.mkOfOrthogonalEqBot both_orthonormal both_total

@[simp] theorem basis_apply(i:Bool×HaarNode):basis i=both i:=by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot both_orthonormal both_total) i
end SHE.NativeTwoChannelNoiseBasis
