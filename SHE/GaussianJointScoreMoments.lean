module

public import SHE.JointGaussianBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.GaussianJointScoreMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  MeasurableGaussianScores GaussianDependentScores
open scoped BigOperators
variable {n r : ℕ}

def scores (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r → State n) (B : Matrix (Fin n) (Fin n) ℝ) (E : State n)
    (x : (Fin r → State n) × State n) : ℝ :=
  (∏ j,secondScore (A j) (D j) (x.1 j))*factor second B E x.2

theorem scores_measurable (second : Bool) (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r → State n) (B : Matrix (Fin n) (Fin n) ℝ) (E : State n) :
    Measurable (scores second A D B E) := by
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro j _
    exact (factor_measurable true (A j) (D j)).comp ((measurable_pi_apply j).comp measurable_fst)
  · exact (factor_measurable second B E).comp measurable_snd

/-- All old covariance scores and one genuine new mean/covariance score
have their fixed moments under the actual old/residual product law. This
uses independence only between the reserved Gaussian fractions; no test
factor is split off from any of these scores. -/
theorem scores_even_moment (second : Bool)
    (A : Fin r → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ j, (A j).PosSemidef)
    (D : Fin r → State n) (hD : ∀ j, D j ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) (A j)).range)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (E : State n) (hE : E ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) B).range) (p : ℕ) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x => |scores second A D B E x|^(2*p)) μ ∧
      (∫ x, |scores second A D B E x|^(2*p) ∂μ) ≤
        ((secondScoreMoment p)^r*productMomentConstant p)*
          ((∏ j,scoreVariance (A j) (D j))*scale second B E)^(2*p) := by
  intro μ
  have hOld := OldIntervalScoreMoments.product_even_moment A hA D hD p
  have hNew := factor_even_moment hB hE second p
  have he (x : (Fin r → State n) × State n) : |scores second A D B E x|^(2*p) =
      |∏ j,secondScore (A j) (D j) (x.1 j)|^(2*p)*|factor second B E x.2|^(2*p) := by
    rw [scores,abs_mul,mul_pow]
  have hi : Integrable (fun x : (Fin r → State n) × State n =>
      |∏ j,secondScore (A j) (D j) (x.1 j)|^(2*p)*|factor second B E x.2|^(2*p)) μ :=
    hOld.1.mul_prod hNew.1
  refine ⟨by simpa only [he] using hi, ?_⟩
  simp_rw [he]
  dsimp only [μ]
  have hfub := integral_prod_mul
    (μ := Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))
    (ν := multivariateGaussian (0 : State n) B)
    (fun y : Fin r → State n => |∏ j,secondScore (A j) (D j) (y j)|^(2*p))
    (fun y : State n => |factor second B E y|^(2*p))
  rw [hfub,hOld.2]
  have hprod : 0 ≤ ∏ j,scoreVariance (A j) (D j) :=
    Finset.prod_nonneg (fun j _ => scoreVariance_nonneg (hA j) (hD j))
  have hnn : 0 ≤ (secondScoreMoment p)^r*(∏ j,scoreVariance (A j) (D j))^(2*p) :=
    mul_nonneg (pow_nonneg (secondScoreMoment_nonneg p) r) (pow_nonneg hprod (2*p))
  have hh := mul_le_mul_of_nonneg_left hNew.2 hnn
  convert! hh using 1
  rw [mul_pow]
  ring

end SHE.GaussianJointScoreMoments
