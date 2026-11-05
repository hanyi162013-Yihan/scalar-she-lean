module

public import SHE.VectorJointRoot
public import SHE.PhysicalJointBlocks
public import SHE.GaussianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.VectorPhysicalRoot
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit GaussianVectorFractions
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianClipMoments GaussianCoordinates
  OldIntervalCovariance OldIntervalVariance StoppedGaussianFeatures StoppedFourier ProfileVariance
open scoped BigOperators NNReal
local instance : Fact (0 < 2*π) := ⟨by positivity⟩
variable {n d r m : ℕ}

def scale (choices : List (Fin r × Fin m)) (factor : Fin m)
    (lo hi : Fin r → ℝ) (A0 ν M : ℝ) (d : ℕ) : ℝ :=
  (2 : ℝ)^(block choices factor).length*A0*(d : ℝ)^(block choices factor).length*
    (∏ j : Fin (block choices factor).length,
      min 1 (ν*sqrt (upperConstant*M)*(hi ((block choices factor).get j)-
        lo ((block choices factor).get j))^(1/4 : ℝ)))

/-- A full root cylinder may select any of the original stopped
observation coordinates. Each old interval keeps its own quarter-power
Bernstein clip, uniformly over all original targets and residual bases. -/
theorem root_even_moment (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i, 0 < σ i) (hσ1 : ∀ i, σ i ≤ 1) (hages : ∀ i, σ i ≤ target i)
    (c : Domain → ℝ) (hc : Measurable c) {M : ℝ} (hcb : ∀ z, 0 ≤ c z ∧ c z ≤ M)
    (lo hi : Fin r → ℝ) (hlo : ∀ j, 0 ≤ lo j) (hgap : ∀ j, lo j < hi j)
    (hstop : ∀ j i, σ i ≤ lo j ∨ hi j ≤ σ i) (B : Matrix (Fin n) (Fin n) ℝ)
    (choices : List (Fin r × Fin m)) (hnd : (choices.map Prod.fst).Nodup) (factor : Fin m)
    (hlen : 0 < (block choices factor).length) (g : Fin d → Fin n)
    (F : State d → ℝ) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hF : ContDiff ℝ (block choices factor).length F)
    (hb : ∀ j, j ≤ (block choices factor).length → ∀ z,
      ‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (mean : State n → State d) (hm : Measurable mean) (p : ℕ) (hp : 0 < p) :
    let A := familyCovariance σ target center c lo hi
    let L := fun _ : Fin r => projection g
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |VectorJointRoot.value choices factor F mean L x|^(2*p)) μ ∧
      (∫ x,|VectorJointRoot.value choices factor F mean L x|^(2*p) ∂μ) ≤
        clipMomentConstant (p*(block choices factor).length)*
          (scale choices factor lo hi A0 ν M d)^(2*p) := by
  intro A L μ
  have hM : 0 ≤ M := (hcb (0,0)).1.trans (hcb (0,0)).2
  let V := fun j => (upperConstant*M*(hi j-lo j)^(1/2 : ℝ)).toNNReal
  have hv0 (j : Fin r) : 0 ≤ upperConstant*M*(hi j-lo j)^(1/2 : ℝ) :=
    mul_nonneg (mul_nonneg upperConstant_pos.le hM) (rpow_nonneg (sub_pos.mpr (hgap j)).le _)
  have hv (j : Fin r) (i : Fin d) :
      Var[(EuclideanSpace.proj (𝕜 := ℝ) i).comp (L j);multivariateGaussian 0 (A j)] ≤ (V j : ℝ) := by
    have he : (EuclideanSpace.proj (𝕜 := ℝ) i).comp (L j) =
        EuclideanSpace.proj (𝕜 := ℝ) (g i) := by ext x; rfl
    rw [he,Real.coe_toNNReal _ (hv0 j)]
    exact coordinate_variance_bound σ target center hσ hσ1 hages c hc hcb
      (hlo j) (hgap j) (hstop j) (g i)
  have hh := VectorJointRoot.root_even_moment A B choices hnd factor hlen F hA0 hν hF hb mean hm L V hv p hp
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hclip (j : Fin (block choices factor).length) :
      min 1 (ν*sqrt (V ((block choices factor).get j) : ℝ)) ≤
        min 1 (ν*sqrt (upperConstant*M)*
          (hi ((block choices factor).get j)-lo ((block choices factor).get j))^(1/4 : ℝ)) := by
    let i := (block choices factor).get j
    have ht := PhysicalOldBlockMoments.physical_variance_power (hv0 i) hM
      (sub_pos.mpr (hgap i)) (by norm_num : 0 ≤ (1 : ℝ)) (le_refl _)
    have hs : sqrt (V i : ℝ) ≤ sqrt (upperConstant*M)*(hi i-lo i)^(1/4 : ℝ) := by
      rw [Real.coe_toNNReal _ (hv0 i)]
      simpa only [one_div,Real.sqrt_eq_rpow] using ht
    apply min_le_min_left
    convert! mul_le_mul_of_nonneg_left hs hν using 1
    ring
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => le_min (by norm_num)
    (mul_nonneg hν (sqrt_nonneg _))) (fun j _ => hclip j)
  unfold scale
  apply mul_le_mul_of_nonneg_left _ (clipMomentConstant_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

end SHE.VectorPhysicalRoot
