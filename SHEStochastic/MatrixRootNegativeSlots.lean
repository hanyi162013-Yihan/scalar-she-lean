module

public import SHEStochastic.MatrixRootTransforms
public import SHEStochastic.NegativeConstantOutput
public import SHEStochastic.MatrixNegativeLocalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixRootNegativeSlots
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.CircleHeat SHE.HaarWeightedHeat
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def count (d : Type*) [Fintype d] : ℝ := 1 + (Fintype.card d : ℝ)^2

theorem count_one : 1 ≤ count d := by unfold count; linarith [sq_nonneg (Fintype.card d : ℝ)]

def normalized (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) : RealL2 →L[ℝ] CircleL2 :=
  (normalizedConstantOutput Λ ρ t hΛ hρ b B hb).comp realEmbed

def negativeSize (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : Domain (d := d)) : ℝ :=
  transformedSize (operator Λ ρ hΛ hρ) v.val

theorem negativeSize_nonneg (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : Domain (d := d)) :
    0 ≤ negativeSize Λ ρ hΛ hρ v := transformedSize_nonneg _ _

theorem negativeSize_sq {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : Domain (d := d)) :
    negativeSize Λ ρ hΛ hρ v ^ 2 ≤ count d * MatrixNegativeLocalization.energy Λ ρ v := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (d × d)) (fun _ => (1 : ℝ))
    (fun q => ‖besselHalf Λ ρ hΛ hρ (realEmbed (entry q.1 q.2 v.val))‖)
  have he : (∑ r : d, ∑ j : d, ‖besselHalf Λ ρ hΛ hρ (realEmbed (entry r j v.val))‖ ^ 2) =
      MatrixNegativeLocalization.energy Λ ρ v := by
    simp only [MatrixNegativeLocalization.energy, besselHalf_norm_sq,
      NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
  change (∑ r : d, ∑ j : d, ‖besselHalf Λ ρ hΛ hρ (realEmbed (entry r j v.val))‖)^2 ≤ _
  have hh' : (∑ r : d, ∑ j : d, ‖besselHalf Λ ρ hΛ hρ (realEmbed (entry r j v.val))‖)^2 ≤
      (Fintype.card d : ℝ)^2 * MatrixNegativeLocalization.energy Λ ρ v := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ← pow_two, Nat.cast_pow, he] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_right (by unfold count; linarith)
    (MatrixNegativeLocalization.energy_nonneg hΛ v))

theorem transformed_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : CircleL2 →L[ℝ] E) (hT : ∀ z, ‖T z‖ ≤ ‖z‖)
    (v : Domain (d := d)) (A : ℝ) (hA : 0 ≤ A) (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ A) :
    transformedSize (T.comp realEmbed) v.val ≤ count d * A := by
  calc
    _ ≤ ∑ r : d, ∑ j : d, A := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro j hj
      exact (hT (realEmbed (entry r j v.val))).trans
        (circle_norm_le_ae_bound _ A (entry_bounded v.val A hv r j))
    _ ≤ count d * A := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [count]
      nlinarith

theorem bounded {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (v : Domain (d := d)) (A : ℝ) (hA : 0 ≤ A)
    (hv : ∀ᵐ x ∂μ, ‖v.val x‖ ≤ A) :
    transformedSize (normalized Λ ρ t hΛ hρ b B hb) v.val ≤ count d * A :=
  transformed_bounded _ (normalizedConstantOutput_contraction hΛ hρ b B hB hb) v A hA hv

theorem output {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (v : Domain (d := d)) :
    transformedSize (normalized Λ ρ t hΛ hρ.le b B hb) v.val ≤
      NegativeConstantOutput.scale Λ ρ t * negativeSize Λ ρ hΛ hρ.le v := by
  dsimp only [negativeSize, transformedSize]
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ =>
    NegativeConstantOutput.output hΛ hρ hρhalf ht ht1 b B hB hb (realEmbed (entry r j v.val))))

theorem mass {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ht : 0 < t) (ht1 : t ≤ 1)
    (v : Domain (d := d)) :
    MatrixRootCalculus.perturbation v ≤ NegativeConstantOutput.scale Λ ρ t * negativeSize Λ ρ hΛ hρ v := by
  apply (MatrixCellEntries.size_le_sum_abs (MatrixRootCalculus.total v)).trans
  change (∑ r : d, ∑ j : d, |MatrixProfileHilbert.mass d Set.univ v.val r j|) ≤ _
  simp only [MatrixCellEntries.mass_entry, Measure.restrict_univ]
  unfold negativeSize transformedSize
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ =>
    NegativeConstantOutput.mass hΛ hρ ht ht1 (entry r j v.val)))

end SHEStochastic.MatrixRootNegativeSlots
