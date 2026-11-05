module
public import SHE.OrthogonalItoChannels
public import SHE.BoundedHilbertItoCell
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.NativeTwoChannelNoiseBasis
open FiniteHaar OrthogonalItoChannels
open scoped NNReal ENNReal
local instance :MeasurableSpace RealHaarInput:=borel _
local instance :BorelSpace RealHaarInput:=⟨rfl⟩

def haar(i:HaarNode):RealHaarInput:=lp.single 2 i (1:ℝ)

theorem haar_orthonormal:Orthonormal ℝ haar:=by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℝ (lp.single (E:=fun _:HaarNode=>ℝ) 2 i (1:ℝ)) (lp.single (E:=fun _:HaarNode=>ℝ) 2 j (1:ℝ))=_
  rw [lp.inner_single_left]
  by_cases h:i=j
  · subst j
    simp
  · simp [lp.single_apply,h,Ne.symm h]

def both(p:Bool×HaarNode):Both RealHaarInput:=if p.1 then left (haar p.2) else right (haar p.2)

theorem both_orthonormal:Orthonormal ℝ both:=by
  classical
  apply orthonormal_iff_ite.mpr
  rintro ⟨b,i⟩ ⟨c,j⟩
  cases b <;> cases c
  · change inner ℝ (right (haar i)) (right (haar j))=_
    rw [(right (C:=RealHaarInput)).inner_map_map]
    simpa only [Prod.mk.injEq,and_self,and_true,true_and] using orthonormal_iff_ite.mp haar_orthonormal i j
  · change inner ℝ (right (haar i)) (left (haar j))=_
    rw [real_inner_comm,inner_left_right]
    simp
  · change inner ℝ (left (haar i)) (right (haar j))=_
    rw [inner_left_right]
    simp
  · change inner ℝ (left (haar i)) (left (haar j))=_
    rw [(left (C:=RealHaarInput)).inner_map_map]
    simpa only [Prod.mk.injEq,and_self,and_true,true_and] using orthonormal_iff_ite.mp haar_orthonormal i j
end SHE.NativeTwoChannelNoiseBasis
