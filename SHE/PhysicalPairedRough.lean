module

public import SHE.PairedRoughBlocks
public import SHE.PhysicalOldBlockMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalPairedRough
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement
  OldIntervalCovariance OldIntervalVariance StoppedGaussianFeatures StoppedFourier ProfileVariance
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianRoughBlockMoments GaussianClipMoments
open scoped NNReal InnerProductSpace BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩

/-- A paired current rough increment retains its fractional current
power and the complementary quarter-power of an original assigned old
gap, under the genuine full old/residual Gaussian product. -/
theorem even_moment {n r k : ℕ} (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (c : Domain → ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ p,0≤c p ∧ c p≤M)
    (lo hi : Fin r → ℝ) (hlo : ∀ j,0≤lo j) (hgap : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r × Fin k)) (hnd : (choices.map Prod.fst).Nodup)
    (factor : Fin k) (i : Fin r) (hchosen : i∈block choices factor) (leaf : Fin n)
    (a : ℝ → ℝ) (ha : Measurable a) {H β χ : ℝ}
    (hH : 0≤H) (hχ : 0≤χ) (hχβ : χ≤β)
    (hholder : ∀ z w,|a z-a w|≤H*|z-w|^β)
    (mean : State n → ℝ) (hm : Measurable mean) (e : ℝ) (p : ℕ) :
    let A := familyCovariance σ target center c lo hi
    let L := fun _ : Fin r => EuclideanSpace.proj (𝕜:=ℝ) leaf
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |PairedRoughBlocks.value choices factor a mean L e x|^(2*p)) μ ∧
      (∫ x,|PairedRoughBlocks.value choices factor a mean L e x|^(2*p) ∂μ) ≤
        GaussianAudit.gaussianAbsMoment (((2*p : ℕ) : ℝ)*(β-χ))*
          ((2 : ℝ)^((block choices factor).length)*H*|e|^χ*
            (upperConstant*M)^((β-χ)/2)*(hi i-lo i)^((β-χ)/4))^(2*p) := by
  intro A L μ
  have hh := PairedRoughBlocks.value_even_moment A B choices hnd factor i hchosen a ha hH hχ hχβ
    hholder mean hm L e p
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hM : 0≤M := (hcb (0,0)).1.trans (hcb (0,0)).2
  have hv := coordinate_variance_bound σ target center hσ hσ1 hages c hc hcb
    (hlo i) (hgap i) (hstop i) leaf
  have hv' : Var[L i;multivariateGaussian 0 (A i)]^((β-χ)/2) ≤
      (upperConstant*M)^((β-χ)/2)*(hi i-lo i)^((β-χ)/4) :=
    PhysicalOldBlockMoments.physical_variance_power (variance_nonneg _ _) hM
      (sub_pos.mpr (hgap i)) (sub_nonneg.mpr hχβ) hv
  have hs : (2 : ℝ)^((block choices factor).length)*H*|e|^χ*
      Var[L i;multivariateGaussian 0 (A i)]^((β-χ)/2) ≤
      (2 : ℝ)^((block choices factor).length)*H*|e|^χ*
        (upperConstant*M)^((β-χ)/2)*(hi i-lo i)^((β-χ)/4) := by
    convert! mul_le_mul_of_nonneg_left hv'
      (show 0≤(2 : ℝ)^((block choices factor).length)*H*|e|^χ by positivity) using 1
    ring
  have hbase : 0≤(2 : ℝ)^((block choices factor).length)*H*|e|^χ*
      Var[L i;multivariateGaussian 0 (A i)]^((β-χ)/2) :=
    mul_nonneg (by positivity) (rpow_nonneg (variance_nonneg _ _) _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hs (2*p))
    (GaussianAudit.gaussianAbsMoment_nonneg _)

end SHE.PhysicalPairedRough
