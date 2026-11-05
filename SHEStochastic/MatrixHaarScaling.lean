module

public import SHEStochastic.MatrixHaarSmooth
public import SHEStochastic.DirectionalJets

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixHaarScaling
open Matrix MatrixHaarAlgebra DirectionalJets Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem inverse_smul (A : Matrix d d ℝ) (hA : IsUnit A) (c : ℝ) (hc : 0<c) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  letI : Invertible c := invertibleOfNonzero hc.ne'
  simpa only [invOf_eq_inv] using Matrix.inv_smul (A := A) c ((Matrix.isUnit_iff_isUnit_det _).mp hA)

theorem sqrt_smul (A : Matrix d d ℝ) (hA : 0≤A) (c : ℝ) (hc : 0≤c) :
    CFC.sqrt (c • A) = Real.sqrt c • CFC.sqrt A := by
  apply CFC.sqrt_unique _ (smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg A))
  rw [smul_mul_smul, ← pow_two, Real.sq_sqrt hc, CFC.sqrt_mul_sqrt_self A hA]

theorem normalizer (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef) (c : ℝ) (hc : 0<c) :
    MatrixHaarAlgebra.normalizer (c • A) (c • B) = Real.sqrt c • MatrixHaarAlgebra.normalizer A B := by
  let S := A⁻¹+B⁻¹
  have hS : S.PosDef := hA.inv.add hB.inv
  have hroot := (MatrixHaarPositive.sqrt_posDef S hS).isUnit
  unfold MatrixHaarAlgebra.normalizer
  rw [inverse_smul A hA.isUnit c hc, inverse_smul B hB.isUnit c hc, ← smul_add]
  rw [sqrt_smul S hS.posSemidef.nonneg c⁻¹ (inv_nonneg.mpr hc.le),
    inverse_smul (CFC.sqrt S) hroot (Real.sqrt c⁻¹) (Real.sqrt_pos.mpr (inv_pos.mpr hc))]
  rw [Real.sqrt_inv, inv_inv]

private theorem scalar (c : ℝ) (hc : 0<c) : c⁻¹*Real.sqrt c=(Real.sqrt c)⁻¹ := by
  have hs : Real.sqrt c≠0 := (Real.sqrt_pos.mpr hc).ne'
  calc
    _ = ((Real.sqrt c)^2)⁻¹*Real.sqrt c :=
      congrArg (fun r : ℝ ↦ r⁻¹*Real.sqrt c) (Real.sq_sqrt hc.le).symm
    _ = _ := by field_simp <;> ring

theorem left (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef) (c : ℝ) (hc : 0<c) :
    MatrixHaarAlgebra.left (c • A) (c • B) = (Real.sqrt c)⁻¹ • MatrixHaarAlgebra.left A B := by
  simp only [MatrixHaarAlgebra.left]
  rw [inverse_smul A hA.isUnit c hc, normalizer A B hA hB c hc, smul_mul_smul, scalar c hc]

theorem right (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef) (c : ℝ) (hc : 0<c) :
    MatrixHaarAlgebra.right (c • A) (c • B) = (Real.sqrt c)⁻¹ • MatrixHaarAlgebra.right A B := by
  simp only [MatrixHaarAlgebra.right]
  rw [inverse_smul B hB.isUnit c hc, normalizer A B hA hB c hc, smul_mul_smul, scalar c hc, smul_neg]

/-- Normalizing two equal-length child masses preserves every actual
mixed derivative, with the same explicit inverse square-root length
factor as the undifferentiated Haar function. -/
theorem children_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hB : ∀ y∈s, ContDiffAt ℝ ∞ B y)
    (hp : ∀ y∈s, (A y).PosDef ∧ (B y).PosDef)
    (x : E) (hx : x∈s) (c : ℝ) (hc : 0<c) (w : List E) :
    jet w (fun y ↦ MatrixHaarAlgebra.left (c • A y) (c • B y)) x =
        (Real.sqrt c)⁻¹ • jet w (fun y ↦ MatrixHaarAlgebra.left (A y) (B y)) x ∧
    jet w (fun y ↦ MatrixHaarAlgebra.right (c • A y) (c • B y)) x =
        (Real.sqrt c)⁻¹ • jet w (fun y ↦ MatrixHaarAlgebra.right (A y) (B y)) x := by
  have hSmooth (y : E) (hy : y∈s) := MatrixHaarSmooth.children (hA y hy) (hB y hy)
    (hp y hy).1 (hp y hy).2 ((show ∀ᶠ z in 𝓝 y, z∈s from hs.mem_nhds hy).mono fun z hz ↦ hp z hz)
  constructor
  · have he : (fun y ↦ MatrixHaarAlgebra.left (c • A y) (c • B y)) =ᶠ[𝓝 x]
        (fun y ↦ (Real.sqrt c)⁻¹ • MatrixHaarAlgebra.left (A y) (B y)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact left (A y) (B y) (hp y hy).1 (hp y hy).2 c hc
    exact (DirectionalJets.congr w he).trans
      (DirectionalJets.const_smul s hs x hx w _ _ (fun y hy ↦ (hSmooth y hy).1))
  · have he : (fun y ↦ MatrixHaarAlgebra.right (c • A y) (c • B y)) =ᶠ[𝓝 x]
        (fun y ↦ (Real.sqrt c)⁻¹ • MatrixHaarAlgebra.right (A y) (B y)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact right (A y) (B y) (hp y hy).1 (hp y hy).2 c hc
    exact (DirectionalJets.congr w he).trans
      (DirectionalJets.const_smul s hs x hx w _ _ (fun y hy ↦ (hSmooth y hy).2))

end SHEStochastic.MatrixHaarScaling
