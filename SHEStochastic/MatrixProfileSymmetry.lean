module

public import SHEStochastic.MatrixProfileHilbert

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixProfileSymmetry
open MeasureTheory Matrix MatrixProfileHilbert MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable (d : Type*) [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

def transposeFiber : Fiber d →L[ℝ] Fiber d :=
  (toVector d).comp ((Matrix.transposeLinearEquiv d d ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp (toMatrix d))

theorem transposeFiber_matrix (v : Fiber d) :
    toMatrix d (transposeFiber d v)=(toMatrix d v)ᵀ := rfl

def transposeProfile : Space d →L[ℝ] Space d := (transposeFiber d).compLpL 2 μ

/-- The actual symmetric matrix-profile Hilbert space is the closed
kernel of transpose minus identity. -/
def symmetric : Submodule ℝ (Space d) := (transposeProfile d-ContinuousLinearMap.id ℝ (Space d)).ker

theorem mem_iff (u : Space d) : u∈symmetric d ↔ ∀ᵐ x ∂μ, (toMatrix d (u x)).IsHermitian := by
  have hT := (transposeFiber d).coeFn_compLp u
  constructor
  · intro hu
    change transposeProfile d u-u=0 at hu
    have he := sub_eq_zero.mp hu
    change ⇑(transposeProfile d u) =ᵐ[μ] fun x => transposeFiber d (u x) at hT
    rw [he] at hT
    filter_upwards [hT] with x hx
    have hm := congrArg (toMatrix d) hx
    rw [transposeFiber_matrix] at hm
    change (toMatrix d (u x))ᴴ=toMatrix d (u x)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hm.symm
  · intro hu
    have he : transposeProfile d u=u := by
      apply Lp.ext
      filter_upwards [hT, hu] with x hx hh
      change (transposeFiber d).compLp u x=u x
      rw [hx]
      apply (coordinates d).injective
      change toMatrix d (transposeFiber d (u x))=toMatrix d (u x)
      rw [transposeFiber_matrix]
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh.eq
    change transposeProfile d u-u=0
    exact sub_eq_zero.mpr he

theorem hermitian (u : symmetric d) : ∀ᵐ x ∂μ, (toMatrix d (u.val x)).IsHermitian :=
  (mem_iff d u.val).mp u.property

theorem mass_eq_integral (s : Set (AddCircle (1 : ℝ))) (u : Space d) :
    mass d s u=∫ x in s, toMatrix d (u x) ∂μ := by
  have hi : Integrable u ((μ).restrict s) := ((Lp.memLp u).integrable (by norm_num : (1 : ENNReal)≤2)).integrableOn
  exact ((toMatrix d).integral_comp_comm hi).symm

theorem mass_hermitian (s : Set (AddCircle (1 : ℝ))) (u : symmetric d) :
    (mass d s u).IsHermitian := by
  have hi : Integrable (fun x => toMatrix d (u.val x)) ((μ).restrict s) :=
    (toMatrix d).integrable_comp (((Lp.memLp u.val).integrable (by norm_num : (1 : ENNReal)≤2)).integrableOn)
  rw [mass_eq_integral]
  change (∫ x in s, toMatrix d (u.val x) ∂μ)ᴴ=∫ x in s, toMatrix d (u.val x) ∂μ
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  calc
    _ = ∫ x in s, toMatrix d (u.val x) j i ∂μ := ((MatrixHaarPairings.entry j i).integral_comp_comm hi).symm
    _ = ∫ x in s, toMatrix d (u.val x) i j ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hermitian d u)] with x hx
      simpa only [Matrix.conjTranspose_apply, star_trivial] using congrArg (fun A : Matrix d d ℝ => A i j) hx.eq
    _ = _ := (MatrixHaarPairings.entry i j).integral_comp_comm hi

/-- Every bounded elliptic covariance profile supplies an actual point
of this symmetric profile space. -/
def realize (P : Profile d) : symmetric d :=
  ⟨MatrixProfileHilbert.realize d P, (mem_iff d _).mpr (by
    filter_upwards [realize_ae d P, P.lower_bound] with x hx hLo
    rw [hx]
    change (P.value x).IsHermitian
    exact (le_trans (smul_nonneg P.lower_pos.le zero_le_one) hLo).posSemidef.isHermitian)⟩

end SHEStochastic.MatrixProfileSymmetry
