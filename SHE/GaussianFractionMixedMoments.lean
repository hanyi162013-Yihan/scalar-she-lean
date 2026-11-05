module

public import SHE.GaussianJointScoreMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.GaussianFractionMixedMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  MeasurableGaussianScores GaussianDependentScores
open scoped BigOperators
variable {n r : ℕ}

def value (second : Fin r→Bool) (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r→State n) (x : Fin r→State n) : ℝ :=
  ∏ j,factor (second j) (A j) (D j) (x j)

theorem measurable_value (second : Fin r→Bool) (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (D : Fin r→State n) : Measurable (value second A D) :=
  Finset.measurable_prod Finset.univ (fun j _ =>
    (factor_measurable (second j) (A j) (D j)).comp (measurable_pi_apply j))

/-- Every old second score and a freshly reserved terminal FIRST score
keep their correct variance degrees under the actual Gaussian fraction
product. No root or rough test is separated from the score product. -/
theorem even_moment (second : Fin r→Bool) (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j,(A j).PosSemidef) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range) (p : ℕ) :
    Integrable (fun x => |value second A D x|^(2*p))
      (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))) ∧
      (∫ x,|value second A D x|^(2*p)
        ∂Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))) ≤
      (productMomentConstant p)^r*(∏ j,scale (second j) (A j) (D j))^(2*p) := by
  have hi (j : Fin r) := (factor_even_moment (hA j) (hD j) (second j) p).1
  have he (x : Fin r→State n) : |value second A D x|^(2*p)=
      ∏ j,|factor (second j) (A j) (D j) (x j)|^(2*p) := by
    rw [value,Finset.abs_prod,Finset.prod_pow]
  refine ⟨?_,?_⟩
  · simp_rw [he]
    exact Integrable.fintype_prod hi
  · simp_rw [he]
    have hfub := integral_fintype_prod_eq_prod
      (μ:=fun j => multivariateGaussian (0 : State n) (A j))
      (fun (j : Fin r) (x : State n) => |factor (second j) (A j) (D j) x|^(2*p))
    change (∫ x : Fin r→State n,∏ j,|factor (second j) (A j) (D j) (x j)|^(2*p)
      ∂Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))=_ at hfub
    rw [hfub]
    have hb := Finset.prod_le_prod₀ (s:=Finset.univ)
      (fun j _ => integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _))
      (fun j _ => (factor_even_moment (hA j) (hD j) (second j) p).2)
    refine hb.trans_eq ?_
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_pow]

/-- The same exact moments hold with any independent residual Gaussian
kept inside all later test factors. -/
theorem residual_even_moment (second : Fin r→Bool) (A : Fin r→Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j,(A j).PosSemidef) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (B : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    Integrable (fun x : (Fin r→State n)×State n => |value second A D x.1|^(2*p)) μ ∧
      (∫ x : (Fin r→State n)×State n,|value second A D x.1|^(2*p) ∂μ) ≤
        (productMomentConstant p)^r*(∏ j,scale (second j) (A j) (D j))^(2*p) := by
  intro μ
  have hh := even_moment second A hA D hD p
  have hl := (measurePreserving_fst (μ:=Measure.pi (fun j => multivariateGaussian (0 : State n) (A j)))
    (ν:=multivariateGaussian (0 : State n) B)).hasLaw
  refine ⟨?_,?_⟩
  · convert! hl.integrable_comp hh.1 using 1
  · convert! (hl.integral_comp (f:=fun x => |value second A D x|^(2*p))
      hh.1.aestronglyMeasurable).trans_le hh.2 using 1

end SHE.GaussianFractionMixedMoments
