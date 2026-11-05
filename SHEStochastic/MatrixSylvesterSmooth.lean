module

public import SHEStochastic.MatrixSylvesterFrobenius
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixSylvesterSmooth
open Matrix Finset MatrixSylvesterFrobenius SHE.FiniteTransport
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Strict positivity of the left Sylvester energy needs only one
nonzero column. No lower spectral bound or diagonalization is assumed. -/
theorem left_positive (S D : Matrix d d ℝ) (hS : S.PosDef) (hD : D≠0) :
    0<pairing D (S*D) := by
  have he : pairing D (S*D)=∑ j, (fun i ↦ D i j) ⬝ᵥ (S*ᵥ(fun i ↦ D i j)) := by
    simp only [pairing, dotProduct, Matrix.mulVec, Matrix.mul_apply]
    exact Finset.sum_comm
  rw [he]
  obtain ⟨i,j,hij⟩ : ∃ i j, D i j≠0 := by
    by_contra hn
    push_neg at hn
    exact hD (Matrix.ext (fun i j ↦ hn i j))
  apply Finset.sum_pos'
  · intro j hj
    simpa only [star_trivial] using hS.posSemidef.dotProduct_mulVec_nonneg (fun i ↦ D i j)
  · refine ⟨j, mem_univ _, ?_⟩
    apply (show 0<star (fun i ↦ D i j) ⬝ᵥ (S*ᵥ(fun i ↦ D i j)) from hS.dotProduct_mulVec_pos ?_)
    intro hz
    exact hij (congrFun hz i)

/-- The derivative of squaring is invertible at every positive
symmetric matrix, even when acting on all real matrix directions. -/
theorem kernel_zero (S D : Matrix d d ℝ) (hS : S.PosDef) (hSD : S*D+D*S=0) : D=0 := by
  by_contra hD
  have hl := left_positive S D hS hD
  have ht : Sᵀ=S := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hr := right_lower S D 0 (fun x ↦ by
    rw [ht, zero_mul]
    simpa only [star_trivial] using hS.posSemidef.dotProduct_mulVec_nonneg x)
  have hh := pairing_add D (S*D) (D*S)
  rw [hSD] at hh
  have hz : pairing D 0=0 := by simp [pairing]
  rw [hz] at hh
  linarith

def derivative (S : Matrix d d ℝ) : Matrix d d ℝ →L[ℝ] Matrix d d ℝ :=
  ContinuousLinearMap.mul ℝ _ S+(ContinuousLinearMap.mul ℝ _).flip S

@[simp] theorem derivative_apply (S D : Matrix d d ℝ) : derivative S D=S*D+D*S := rfl

theorem derivative_injective (S : Matrix d d ℝ) (hS : S.PosDef) :
    Function.Injective (derivative S) := by
  intro X Y hXY
  have hz : derivative S (X-Y)=0 := by rw [map_sub, hXY, sub_self]
  exact sub_eq_zero.mp (kernel_zero S (X-Y) hS (by simpa using hz))

/-- The actual Sylvester derivative as a continuous linear equivalence. -/
def equivalence (S : Matrix d d ℝ) (hS : S.PosDef) :
    Matrix d d ℝ ≃L[ℝ] Matrix d d ℝ :=
  (LinearEquiv.ofBijective (derivative S).toLinearMap
    ⟨derivative_injective S hS,
      LinearMap.injective_iff_surjective.mp (derivative_injective S hS)⟩).toContinuousLinearEquiv

@[simp] theorem equivalence_apply (S D : Matrix d d ℝ) (hS : S.PosDef) :
    equivalence S hS D=S*D+D*S := rfl

theorem hasFDerivAt_square (S : Matrix d d ℝ) :
    HasFDerivAt (fun A : Matrix d d ℝ ↦ A*A) (derivative S) S := by
  have hi : HasFDerivAt (fun A : Matrix d d ℝ ↦ A)
      (ContinuousLinearMap.id ℝ (Matrix d d ℝ)) S := hasFDerivAt_id S
  convert! hi.mul' hi using 1

/-- A smooth local inverse of matrix squaring is obtained from the
proved Sylvester isomorphism, rather than taken as an input theorem. -/
theorem smooth_local_inverse (S : Matrix d d ℝ) (hS : S.PosDef) :
    ∃ f : Matrix d d ℝ → Matrix d d ℝ,
      ContDiffAt ℝ ⊤ f (S*S) ∧ f (S*S)=S ∧
        ∀ᶠ D in 𝓝 S, f (D*D)=D := by
  have hc : ContDiffAt ℝ ⊤ (fun A : Matrix d d ℝ ↦ A*A) S :=
    (contDiff_id.mul contDiff_id).contDiffAt
  have hd : HasFDerivAt (fun A : Matrix d d ℝ ↦ A*A)
      (equivalence S hS).toContinuousLinearMap S := by
    convert hasFDerivAt_square S using 1
    ext D
    rfl
  let f := hc.localInverse hd (by simp)
  refine ⟨f, hc.to_localInverse hd (by simp), hc.localInverse_apply_image hd (by simp), ?_⟩
  exact (hc.hasStrictFDerivAt' hd (by simp)).eventually_left_inverse

end SHEStochastic.MatrixSylvesterSmooth
