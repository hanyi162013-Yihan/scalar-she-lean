module

public import SHEStochastic.MatrixProfileEntries
public import SHEStochastic.MatrixActualColumnCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixCellEntries
open MeasureTheory Matrix SHE SHE.FiniteHaar SHE.DyadicApproximation MatrixProfileHilbert MatrixProfileEntries
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem mass_entry (s : Set (AddCircle (1 : ℝ))) (u : Space d) (r j : d) :
    mass d s u r j = ∫ x in s, entry r j u x ∂μ := by
  let L := L2EuclideanCoordinates.projection (r,j)
  have hi : Integrable u ((μ).restrict s) := ((Lp.memLp u).integrable (by norm_num : (1 : ENNReal) ≤ 2)).integrableOn
  calc
    _ = L (∫ x in s, u x ∂μ) := rfl
    _ = ∫ x in s, L (u x) ∂μ := (L.integral_comp_comm hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (entry_ae u r j)] with x hx
      exact hx.symm

/-- The scalar dyadic averaging formula is precisely normalized
integration on the actual circle cell, including real input embedding. -/
theorem localAverage_integral (n : ℕ) (z : Grid n) (u : RealL2) :
    localAverage n (realEmbed u) z = (((2 ^ n : ℕ) : ℝ)) * ∫ x in cellSet n z, u x ∂μ := by
  have hi : Integrable u μ := (Lp.memLp u).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hs := measurableSet_cellSet n z
  have he : inner ℂ (cellIndicator n z) (realEmbed u) = Complex.ofRealCLM (∫ x in cellSet n z, u x ∂μ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, Complex.ofRealCLM ((cellSet n z).indicator u x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [cellIndicator_ae n z, realEmbed_ae u] with x hx hy
        rw [hx, hy]
        by_cases hm : x ∈ cellSet n z <;> simp [hm, RCLike.inner_apply]
      _ = Complex.ofRealCLM (∫ x, (cellSet n z).indicator u x ∂μ) :=
        Complex.ofRealCLM.integral_comp_comm (hi.indicator hs)
      _ = _ := by rw [integral_indicator hs]
  change (((2 ^ n : ℕ) : ℝ)) * (inner ℂ (cellIndicator n z) (realEmbed u)).re = _
  rw [he]
  rfl

theorem normalized_entry (p : List Bool) (b : Bool)
    (u : MatrixPhysicalColumnSmooth.Domain (d := d)) (r j : d) :
    MatrixActualColumnCalculus.normalizedMass p b u r j =
      localAverage (p.length+1) (realEmbed (entry r j u.val)) (bottomLeaf p b) := by
  rw [localAverage_integral]
  change (MatrixActualColumnCalculus.childLength p)⁻¹ *
    mass d (cellSet (p.length+1) (bottomLeaf p b)) u.val r j = _
  rw [mass_entry]
  simp only [MatrixActualColumnCalculus.childLength, inv_inv]

/-- Scalar entries of the actual Hilbert profile restriction agree
with the existing scalar physical cell restriction, almost everywhere. -/
theorem restricted_entry (n : ℕ) (z : Grid n) (u : Space d) (r j : d) :
    realEmbed (entry r j (MatrixPhysicalColumnMap.restriction (cellSet n z) (measurableSet_cellSet n z) u)) =
      cellRestriction n z (realEmbed (entry r j u)) := by
  let v := MatrixPhysicalColumnMap.restriction (cellSet n z) (measurableSet_cellSet n z) u
  apply Lp.ext
  filter_upwards [realEmbed_ae (entry r j v), entry_ae v r j,
    MatrixPhysicalColumnMap.restriction_ae (cellSet n z) (measurableSet_cellSet n z) u,
    cellRestriction_ae n z (realEmbed (entry r j u)), realEmbed_ae (entry r j u), entry_ae u r j]
      with x hv he hr hc hb hu
  change realEmbed (entry r j v) x = _
  rw [hv, he, hc, hr]
  by_cases hx : x ∈ cellSet n z <;> simp [hx, hb, hu]

theorem size_le_sum_abs (A : Matrix d d ℝ) :
    MatrixFrobeniusNorm.size A ≤ ∑ r : d, ∑ j : d, |A r j| := by
  apply (sq_le_sq₀ (MatrixFrobeniusNorm.nonneg _) (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)))).mp
  rw [MatrixFrobeniusNorm.square]
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun p : d × d => |A p.1 p.2|) (fun p _ => abs_nonneg _)
  simpa only [Fintype.sum_prod_type, sq_abs, SHE.FiniteTransport.frobeniusSq] using hh

end SHEStochastic.MatrixCellEntries
