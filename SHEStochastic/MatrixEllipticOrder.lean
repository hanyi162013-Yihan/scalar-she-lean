module

public import SHEStochastic.MatrixEllipticSize

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixEllipticOrder
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Inverse ellipticity for actual real symmetric covariance matrices,
proved by scalar spectral calculus without a complex-algebra hypothesis. -/
theorem inverse_bounds (A : Matrix d d ℝ) (hp : A.PosDef) (m U : ℝ) (hm : 0 < m)
    (hLo : m • (1 : Matrix d d ℝ) ≤ A) (hHi : A ≤ U • (1 : Matrix d d ℝ)) :
    U⁻¹ • (1 : Matrix d d ℝ) ≤ A⁻¹ ∧ A⁻¹ ≤ m⁻¹ • (1 : Matrix d d ℝ) := by
  have hsa := hp.posSemidef.nonneg.isSelfAdjoint
  have hl : ∀ t ∈ spectrum ℝ A, m ≤ t :=
    (algebraMap_le_iff_le_spectrum hsa).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hLo)
  have hu : ∀ t ∈ spectrum ℝ A, t ≤ U :=
    (le_algebraMap_iff_spectrum_le hsa).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hHi)
  have hn : ∀ t ∈ spectrum ℝ A, t ≠ 0 := fun t ht => (hm.trans_le (hl t ht)).ne'
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (spectrum ℝ A) := continuousOn_id.inv₀ hn
  have he : cfc (fun t : ℝ => t⁻¹) A = A⁻¹ := by
    rw [cfc_ringInverse_id (R := ℝ) A hp.isUnit hsa, Matrix.nonsing_inv_eq_ringInverse]
  have hleft := algebraMap_le_cfc (fun t : ℝ => t⁻¹) U⁻¹ A (fun t ht => by
    simpa only [one_div] using one_div_le_one_div_of_le (hm.trans_le (hl t ht)) (hu t ht)) hc hsa
  have hright := cfc_le_algebraMap (fun t : ℝ => t⁻¹) m⁻¹ A (fun t ht => by
    simpa only [one_div] using one_div_le_one_div_of_le hm (hl t ht)) hc hsa
  rw [he] at hleft hright
  simpa only [Algebra.algebraMap_eq_smul_one] using And.intro hleft hright

end SHEStochastic.MatrixEllipticOrder
