module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HilbertTrace
open scoped ENNReal InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {I J K E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

def energy (A : E →L[𝕜] F) (b : HilbertBasis I 𝕜 E) (c : HilbertBasis J 𝕜 F) (ij : I × J) :=
  ‖inner 𝕜 (c ij.2) (A (b ij.1))‖^2

omit [CompleteSpace E] in
theorem basis_sq (b : HilbertBasis I 𝕜 E) (x : E) :
    Summable (fun i => ‖inner 𝕜 (b i) x‖^2) ∧
      (∑' i, ‖inner 𝕜 (b i) x‖^2)=‖x‖^2 := by
  constructor
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_two,HilbertBasis.repr_apply_apply] using
      (lp.memℓp (b.repr x)).summable (by norm_num)
  · have hh := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) (b.repr x)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,HilbertBasis.repr_apply_apply,
      LinearIsometryEquiv.norm_map] using hh.symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Full double square-summability follows from the actual basis trace. -/
theorem matrix_summable (A : E →L[𝕜] F) (b : HilbertBasis I 𝕜 E) (c : HilbertBasis J 𝕜 F)
    (hA : Summable (fun i => ‖A (b i)‖^2)) : Summable (energy A b c) := by
  apply (summable_prod_of_nonneg (fun ij => sq_nonneg _)).mpr
  constructor
  · exact fun i => (basis_sq c (A (b i))).1
  · simpa only [energy,(basis_sq c _).2] using hA

/-- A genuine operator and its adjoint have the same finite trace
energy. This is derived by Parseval and justified double summation. -/
theorem adjoint_trace (A : E →L[𝕜] F) (b : HilbertBasis I 𝕜 E) (c : HilbertBasis J 𝕜 F)
    (hA : Summable (fun i => ‖A (b i)‖^2)) :
    Summable (fun j => ‖A.adjoint (c j)‖^2) ∧
      (∑' j, ‖A.adjoint (c j)‖^2)=∑' i, ‖A (b i)‖^2 := by
  have hm := matrix_summable A b c hA
  have hrow (j : J) : (∑' i, energy A b c (i,j))=‖A.adjoint (c j)‖^2 := by
    calc
      _ = ∑' i, ‖inner 𝕜 (b i) (A.adjoint (c j))‖^2 := by
        apply tsum_congr
        intro i
        rw [ContinuousLinearMap.adjoint_inner_right]
        exact congrArg (fun r : ℝ => r^2) (norm_inner_symm _ _)
      _ = _ := (basis_sq b _).2
  have hs : Summable (fun j => ‖A.adjoint (c j)‖^2) := by
    have hp := hm.prod_symm.prod
    change Summable (fun j : J => ∑' i : I, energy A b c (i,j)) at hp
    simpa only [hrow] using hp
  refine ⟨hs, ?_⟩
  calc
    _ = ∑' j, ∑' i, energy A b c (i,j) := by simp only [hrow]
    _ = ∑' ji : J × I, energy A b c (ji.2,ji.1) := hm.prod_symm.tsum_prod.symm
    _ = ∑' ij, energy A b c ij := (Equiv.prodComm J I).tsum_eq _
    _ = ∑' i, ∑' j, energy A b c (i,j) := hm.tsum_prod
    _ = _ := by simp only [energy,(basis_sq c _).2]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Composition on the output side preserves square-summable columns. -/
theorem left_comp (A : E →L[𝕜] F) (S : F →L[𝕜] G) (b : HilbertBasis I 𝕜 E)
    (hA : Summable (fun i => ‖A (b i)‖^2)) :
    Summable (fun i => ‖(S.comp A) (b i)‖^2) ∧
      (∑' i, ‖(S.comp A) (b i)‖^2) ≤ ‖S‖^2*∑' i, ‖A (b i)‖^2 := by
  have hb (i : I) : ‖(S.comp A) (b i)‖^2 ≤ ‖S‖^2*‖A (b i)‖^2 := by
    simpa only [ContinuousLinearMap.comp_apply,mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm (A (b i))) 2
  have hs := Summable.of_nonneg_of_le (fun i => sq_nonneg _) hb (hA.mul_left (‖S‖^2))
  refine ⟨hs, ?_⟩
  simpa only [tsum_mul_left] using hs.tsum_le_tsum hb (hA.mul_left (‖S‖^2))

/-- The right-composition ideal estimate is proved using the genuine
adjoint and Parseval. The right factor may share arbitrary randomness
with the kernel when this deterministic theorem is applied pathwise. -/
theorem right_comp (A : E →L[𝕜] F) (R : G →L[𝕜] E)
    (b : HilbertBasis I 𝕜 E) (c : HilbertBasis J 𝕜 F) (g : HilbertBasis K 𝕜 G)
    (hA : Summable (fun i => ‖A (b i)‖^2)) :
    Summable (fun k => ‖(A.comp R) (g k)‖^2) ∧
      (∑' k, ‖(A.comp R) (g k)‖^2) ≤ ‖R‖^2*∑' i, ‖A (b i)‖^2 := by
  have ha := adjoint_trace A b c hA
  have hc := left_comp A.adjoint R.adjoint c ha.1
  have hb := adjoint_trace (R.adjoint.comp A.adjoint) c g hc.1
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint] at hb
  refine ⟨hb.1, ?_⟩
  rw [hb.2]
  calc
    _ ≤ ‖R.adjoint‖^2*∑' j, ‖A.adjoint (c j)‖^2 := hc.2
    _ = _ := by rw [ha.2,LinearIsometryEquiv.norm_map]

end SHE.HilbertTrace
