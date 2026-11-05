module

public import SHE.JointGaussianBlocks
public import SHE.PhysicalOldBlockMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.PhysicalJointBlocks
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement GaussianAudit
  OldIntervalCovariance OldIntervalVariance StoppedGaussianFeatures StoppedFourier ProfileVariance
  GaussianAssignmentBlocks GaussianRoughBlocks JointGaussianBlocks GaussianClipMoments
open scoped NNReal BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The physical old-gap bound remains valid with a genuine random
residual base inside every rough block. -/
theorem rough_block_even_moment {n r k : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (c : Domain → ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M)
    (lo hi : Fin r → ℝ) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (i : Fin r) (hchosen : i ∈ block choices factor) (leaf : Fin n)
    (a : ℝ → ℝ) (ha : Measurable a) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ z w, |a z-a w| ≤ H*|z-w|^β)
    (mean : State n → ℝ) (hm : Measurable mean) (p : ℕ) :
    let A := familyCovariance σ target center c lo hi
    let L := fun _ : Fin r => EuclideanSpace.proj (𝕜 := ℝ) leaf
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |jointBlock choices factor a mean L x|^(2*p)) μ ∧
      (∫ x, |jointBlock choices factor a mean L x|^(2*p) ∂μ) ≤
        gaussianAbsMoment (((2*p : ℕ) : ℝ)*β)*
          ((2 : ℝ)^((block choices factor).length-1)*H*(upperConstant*M)^(β/2)*
            (hi i-lo i)^(β/4))^(2*p) := by
  intro A L μ
  have hh := JointGaussianBlocks.rough_block_even_moment A B choices hnd factor i hchosen a ha
    mean hm L hH hβ hholder p
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hM : 0 ≤ M := (hcb (0,0)).1.trans (hcb (0,0)).2
  have hv := coordinate_variance_bound σ target center hσ hσ1 hages c hc hcb
    (hlo i) (hgap i) (hstop i) leaf
  have hp := PhysicalOldBlockMoments.physical_variance_power
    (variance_nonneg (L i) (multivariateGaussian (0 : State n) (A i))) hM
    (sub_pos.mpr (hgap i)) hβ hv
  have hs : (2 : ℝ)^((block choices factor).length-1)*H*
      Var[L i;multivariateGaussian 0 (A i)]^(β/2) ≤
      (2 : ℝ)^((block choices factor).length-1)*H*(upperConstant*M)^(β/2)*(hi i-lo i)^(β/4) := by
    convert! mul_le_mul_of_nonneg_left hp
      (show 0 ≤ (2 : ℝ)^((block choices factor).length-1)*H by positivity) using 1
    ring
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg (mul_nonneg (by positivity) hH) (rpow_nonneg (variance_nonneg _ _) _)) hs _)
    (gaussianAbsMoment_nonneg _)

/-- Every clip of the physical root block keeps its own original old
interval. Correlation with its score or the residual does not remove it. -/
theorem root_block_even_moment {n r k : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (c : Domain → ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ M)
    (lo hi : Fin r → ℝ) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (hlen : 0 < (block choices factor).length) (leaf : Fin n)
    (f : ℕ → ℝ → ℝ) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ∀ j, j < (block choices factor).length → ∀ z, HasDerivAt (f j) (f (j+1) z) z)
    (hfb : ∀ j, j ≤ (block choices factor).length → ∀ z, |f j z| ≤ A0*ν^j)
    (mean : State n → ℝ) (hm : Measurable mean) (p : ℕ) :
    let A := familyCovariance σ target center c lo hi
    let L := fun _ : Fin r => EuclideanSpace.proj (𝕜 := ℝ) leaf
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |jointBlock choices factor (f 0) mean L x|^(2*p)) μ ∧
      (∫ x, |jointBlock choices factor (f 0) mean L x|^(2*p) ∂μ) ≤
        clipMomentConstant (p*(block choices factor).length)*
          ((2 : ℝ)^((block choices factor).length)*A0*
            (∏ j : Fin (block choices factor).length, min 1
              (ν*sqrt (upperConstant*M)*(hi ((block choices factor).get j)-lo ((block choices factor).get j))^(1/4 : ℝ))))^(2*p) := by
  intro A L μ
  have hh := JointGaussianBlocks.root_block_even_moment A B choices hnd factor hlen f hA0 hν hf hfb mean hm L p
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hM : 0 ≤ M := (hcb (0,0)).1.trans (hcb (0,0)).2
  have hclip (j : Fin (block choices factor).length) :
      min 1 (ν*sqrt (Var[L ((block choices factor).get j);
        multivariateGaussian 0 (A ((block choices factor).get j))])) ≤
      min 1 (ν*sqrt (upperConstant*M)*
        (hi ((block choices factor).get j)-lo ((block choices factor).get j))^(1/4 : ℝ)) := by
    let i := (block choices factor).get j
    have hv := coordinate_variance_bound σ target center hσ hσ1 hages c hc hcb
      (hlo i) (hgap i) (hstop i) leaf
    have hp := PhysicalOldBlockMoments.physical_variance_power
      (variance_nonneg (L i) (multivariateGaussian (0 : State n) (A i))) hM
      (sub_pos.mpr (hgap i)) (by norm_num : 0 ≤ (1 : ℝ)) hv
    have hp' : sqrt (Var[L i;multivariateGaussian 0 (A i)]) ≤
        sqrt (upperConstant*M)*(hi i-lo i)^(1/4 : ℝ) := by
      simpa only [one_div, Real.sqrt_eq_rpow] using hp
    apply min_le_min_left
    convert! mul_le_mul_of_nonneg_left hp' hν using 1
    ring
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun j _ => le_min (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hν (sqrt_nonneg _)))
    (fun j _ => hclip j)
  have hs := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ (2 : ℝ)^((block choices factor).length)*A0 by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs _) (clipMomentConstant_nonneg _)

end SHE.PhysicalJointBlocks
