module

public import SHEStochastic.MatrixProfileCongruence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixFactorCongruence
open MeasureTheory MatrixInfiniteHaar
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The complete infinite Haar factor depends only on the actual
spatial covariance, not its representative or chosen bounding metadata. -/
theorem factor (P Q : Profile d)
    (h : P.value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] Q.value) :
    MatrixInfiniteHaar.factor P=MatrixInfiniteHaar.factor Q := by
  have he := MatrixProfileCongruence.realize_eq P Q h
  have hc (i : d × SHE.FiniteHaar.HaarNode) :
      MatrixInfiniteHaar.factor P (lp.single 2 i 1)=MatrixInfiniteHaar.factor Q (lp.single 2 i 1) := by
    rw [← MatrixHaarHigherFamily.column_realize P i.1 i.2,
      ← MatrixHaarHigherFamily.column_realize Q i.1 i.2,he]
  let e : HilbertBasis (d × SHE.FiniteHaar.HaarNode) ℝ (Input (d := d)) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ (Input (d := d)))
  have hb (i : d × SHE.FiniteHaar.HaarNode) : e i=lp.single 2 i 1 := by
    rw [← HilbertBasis.repr_symm_single e i]
    rfl
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span)
  rintro _ ⟨i,rfl⟩
  rw [hb,hc]

end SHEStochastic.MatrixFactorCongruence
