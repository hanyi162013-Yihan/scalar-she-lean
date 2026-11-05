module

public import SHEStochastic.MatrixPhysicalColumnMap
public import SHEStochastic.L2EuclideanCoordinates
public import SHEStochastic.MatrixProfileNorms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixProfileEntries
open MeasureTheory Matrix SHE SHE.FiniteHaar SHE.DyadicApproximation MatrixInfiniteHaar MatrixProfileHilbert
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def entry (r s : d) : Space d →L[ℝ] RealL2 :=
  (L2EuclideanCoordinates.projection (r,s)).compLpL 2 μ
def component (r : d) : Physical (d := d) →L[ℝ] RealL2 :=
  (L2EuclideanCoordinates.projection r).compLpL 2 μ

theorem entry_ae (u : Space d) (r s : d) : ⇑(entry r s u) =ᵐ[μ] fun x => u x (r,s) :=
  (L2EuclideanCoordinates.projection (r,s)).coeFn_compLp u
theorem component_ae (u : Physical (d := d)) (r : d) : ⇑(component r u) =ᵐ[μ] fun x => u x r :=
  (L2EuclideanCoordinates.projection r).coeFn_compLp u

theorem entry_bounded (u : Space d) (B : ℝ) (hu : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) (r s : d) :
    ∀ᵐ x ∂μ, ‖realEmbed (entry r s u) x‖ ≤ B := by
  filter_upwards [entry_ae u r s, realEmbed_ae (entry r s u), hu] with x he hr hx
  rw [hr, Complex.norm_real, he]
  exact (PiLp.norm_apply_le (u x) (r,s)).trans hx

/-- Constant matrix coefficients commute with arbitrary scalar
spatial transforms through the literal entrywise column formula. -/
theorem action_component (u : Space d) (i r : d) (C : Matrix d d ℝ) :
    component r (MatrixPhysicalColumnMap.action i u C) = ∑ j : d, C j i • entry r j u := by
  have he : ∀ᵐ x ∂μ, ∀ j : d, entry r j u x = u x (r,j) :=
    ae_all_iff.mpr (fun j => entry_ae u r j)
  have hsm : ∀ᵐ x ∂μ, ∀ j : d, (C j i • entry r j u) x = C j i • (entry r j u x) :=
    ae_all_iff.mpr (fun j => Lp.coeFn_smul (C j i) (entry r j u))
  apply Lp.ext
  filter_upwards [component_ae (MatrixPhysicalColumnMap.action i u C) r,
    MatrixPhysicalColumnMap.action_ae i u C, Lp.coeFn_finsetSum Finset.univ (fun j : d => C j i • entry r j u),
    he, hsm] with x hc ha hs he hm
  rw [hc, ha, MatrixHaarRootColumns.column_apply, hs]
  simp only [Finset.sum_apply]
  change (∑ j : d, u x (r,j) * C j i) = _
  apply Finset.sum_congr rfl
  intro j hj
  rw [hm j, he j]
  exact mul_comm _ _

theorem entry_size (C : Matrix d d ℝ) (r s : d) : |C r s| ≤ MatrixFrobeniusNorm.size C := by
  have hh := PiLp.norm_apply_le (toVector d C) (r,s)
  rw [norm_vector] at hh
  exact hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def transformedSize (T : RealL2 →L[ℝ] E) (u : Space d) : ℝ := ∑ r : d, ∑ s : d, ‖T (entry r s u)‖

theorem transformedSize_nonneg (T : RealL2 →L[ℝ] E) (u : Space d) : 0 ≤ transformedSize T u :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem transformed_action (T : RealL2 →L[ℝ] E) (u : Space d) (i r : d) (C : Matrix d d ℝ) :
    ‖T (component r (MatrixPhysicalColumnMap.action i u C))‖ ≤
      MatrixFrobeniusNorm.size C * transformedSize T u := by
  rw [action_component, map_sum]
  simp only [map_smul]
  calc
    _ ≤ ∑ j : d, ‖C j i • T (entry r j u)‖ := norm_sum_le _ _
    _ = ∑ j : d, |C j i| * ‖T (entry r j u)‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j : d, MatrixFrobeniusNorm.size C * ‖T (entry r j u)‖ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (entry_size C j i) (norm_nonneg _))
    _ = MatrixFrobeniusNorm.size C * ∑ j : d, ‖T (entry r j u)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun j _ => norm_nonneg (T (entry a j u)))) (Finset.mem_univ r))
      (MatrixFrobeniusNorm.nonneg _)

end SHEStochastic.MatrixProfileEntries
