module

public import SHE.TwoFreshGaussianFractions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.NativeFirstOldScoreMoments
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAudit MeasurableGaussianScores GaussianDependentScores
open scoped BigOperators
variable {n r:ℕ}

/-- The native first score is retained, while the second fresh law has
NO mark. This is the score product needed for omitted-baseline terms. -/
def scores (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n)
    (R:Matrix (Fin n) (Fin n) ℝ) (E:State n)
    (z:(Fin r→State n)×(State n×State n)):ℝ:=
  (∏j,secondScore (A j) (D j) (z.1 j))*firstScore R E z.2.1

theorem scores_even_moment
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:Matrix (Fin n) (Fin n) ℝ) (hR:R.PosSemidef)
    (E:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range) (p:ℕ):
    let ν:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
    Integrable (fun z=>|scores A D R E z|^(2*p)) ν ∧
      (∫z,|scores A D R E z|^(2*p) ∂ν)≤
        ((secondScoreMoment p)^r*productMomentConstant p)*
          ((∏j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E))^(2*p):=by
  intro ν
  have ho:=OldIntervalScoreMoments.product_even_moment A hA D hD p
  have hr:=factor_even_moment hR hE false p
  have hri:=hr.1.comp_fst (multivariateGaussian (0:State n) C)
  have he(z:(Fin r→State n)×(State n×State n)):
      |scores A D R E z|^(2*p)=
        |∏j,secondScore (A j) (D j) (z.1 j)|^(2*p)*|factor false R E z.2.1|^(2*p):=by
    simp only [scores,factor,Bool.false_eq_true,ite_false,abs_mul,mul_pow]
  refine ⟨by simp_rw [he];exact ho.1.mul_prod hri,?_⟩
  simp_rw [he]
  dsimp only [ν]
  have hfub:=integral_prod_mul
    (μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))
    (ν:=(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
    (fun old:Fin r→State n=>|∏j,secondScore (A j) (D j) (old j)|^(2*p))
    (fun fresh:State n×State n=>|factor false R E fresh.1|^(2*p))
  rw [hfub,ho.2]
  have hrest:(∫fresh:State n×State n,|factor false R E fresh.1|^(2*p)
      ∂(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))=
      ∫y,|factor false R E y|^(2*p) ∂multivariateGaussian (0:State n) R:=by
    rw [integral_prod _ hri]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hrest]
  have hv0:0≤∏j,scoreVariance (A j) (D j):=
    Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j))
  have hc:0≤(secondScoreMoment p)^r*(∏j,scoreVariance (A j) (D j))^(2*p):=
    mul_nonneg (pow_nonneg (secondScoreMoment_nonneg p) _) (pow_nonneg hv0 _)
  have hs:=mul_le_mul_of_nonneg_left hr.2 hc
  convert! hs using 1
  simp only [scale,Bool.false_eq_true,ite_false,mul_pow]
  ring

end SHE.NativeFirstOldScoreMoments
