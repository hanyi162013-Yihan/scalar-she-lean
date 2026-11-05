module

public import SHE.GaussianConvolution
public import SHE.GaussianJointScoreMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.TwoFreshGaussianFractions
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution
  GaussianAudit MeasurableGaussianScores GaussianDependentScores
open scoped BigOperators MeasureTheory
variable {X:Type*} [MeasurableSpace X] {n r:ℕ}

/-- The two independent fresh fractions are added only inside the test;
their two physical scores remain on their original fractions. -/
def merge (z:X×(State n×State n)):X×State n:=(z.1,z.2.1+z.2.2)

theorem merge_preserving (ν:Measure X) [SFinite ν]
    {R C:Matrix (Fin n) (Fin n) ℝ} (hR:R.PosSemidef) (hC:C.PosSemidef):
    MeasurePreserving (merge (X:=X))
      (ν.prod ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))
      (ν.prod (multivariateGaussian (0:State n) (R+C))):=by
  have hadd:MeasurePreserving (fun z:State n×State n=>z.1+z.2)
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
      (multivariateGaussian (0:State n) (R+C)):=by
    refine ⟨measurable_fst.add measurable_snd,?_⟩
    exact multivariateGaussian_convolution R C hR hC
  exact (MeasurePreserving.id ν).prod hadd

/-- Every correlated old/root/rough moment is unchanged by splitting the
full residual into the two genuine independent fresh Gaussian fractions. -/
theorem integral_merge (ν:Measure X) [SFinite ν]
    {R C:Matrix (Fin n) (Fin n) ℝ} (hR:R.PosSemidef) (hC:C.PosSemidef)
    (F:X×State n→ℝ) (hF:Measurable F):
    (Integrable (fun z=>F (merge z))
      (ν.prod ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))) ↔
        Integrable F (ν.prod (multivariateGaussian (0:State n) (R+C)))) ∧
    (∫z,F (merge z) ∂ν.prod ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))=
      ∫z,F z ∂ν.prod (multivariateGaussian (0:State n) (R+C)):=by
  have hp:=merge_preserving ν hR hC
  refine ⟨hp.integrable_comp hF.aestronglyMeasurable,?_⟩
  have he:=integral_map
    (μ:=ν.prod ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C)))
    hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

def scores (second:Bool) (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n)
    (R C:Matrix (Fin n) (Fin n) ℝ) (E V:State n)
    (z:(Fin r→State n)×(State n×State n)):ℝ:=
  (∏j,secondScore (A j) (D j) (z.1 j))*firstScore R E z.2.1*factor second C V z.2.2

theorem scores_even_moment (second:Bool)
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (R C:Matrix (Fin n) (Fin n) ℝ) (hR:R.PosSemidef) (hC:C.PosSemidef)
    (E V:State n) (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    (hV:V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range) (p:ℕ):
    let ν:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
      ((multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
    Integrable (fun z=>|scores second A D R C E V z|^(2*p)) ν ∧
      (∫z,|scores second A D R C E V z|^(2*p) ∂ν)≤
        ((secondScoreMoment p)^r*(productMomentConstant p)^2)*
          ((∏j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E)*scale second C V)^(2*p):=by
  intro ν
  have ho:=OldIntervalScoreMoments.product_even_moment A hA D hD p
  have hr:=factor_even_moment hR hE false p
  have hc:=factor_even_moment hC hV second p
  have he(z:(Fin r→State n)×(State n×State n)):
      |scores second A D R C E V z|^(2*p)=
        |∏j,secondScore (A j) (D j) (z.1 j)|^(2*p)*
          (|factor false R E z.2.1|^(2*p)*|factor second C V z.2.2|^(2*p)):=by
    simp only [scores,factor,Bool.false_eq_true,if_false,abs_mul,mul_pow]
    ring
  refine ⟨by simp_rw [he];exact ho.1.mul_prod (hr.1.mul_prod hc.1),?_⟩
  simp_rw [he]
  dsimp only [ν]
  have hfub:=integral_prod_mul
    (μ:=Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))
    (ν:=(multivariateGaussian (0:State n) R).prod (multivariateGaussian (0:State n) C))
    (fun old:Fin r→State n=>|∏j,secondScore (A j) (D j) (old j)|^(2*p))
    (fun fresh:State n×State n=>|factor false R E fresh.1|^(2*p)*|factor second C V fresh.2|^(2*p))
  rw [hfub]
  have hfub2:=integral_prod_mul
    (μ:=multivariateGaussian (0:State n) R) (ν:=multivariateGaussian (0:State n) C)
    (fun y:State n=>|factor false R E y|^(2*p)) (fun y:State n=>|factor second C V y|^(2*p))
  rw [hfub2,ho.2]
  have hv0:0≤∏j,scoreVariance (A j) (D j):=
    Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j))
  have hconst:0≤(secondScoreMoment p)^r*(∏j,scoreVariance (A j) (D j))^(2*p):=by
    exact mul_nonneg (pow_nonneg (secondScoreMoment_nonneg p) _) (pow_nonneg hv0 _)
  have hs:=mul_le_mul_of_nonneg_left
    (mul_le_mul hr.2 hc.2 (integral_nonneg (fun _=>pow_nonneg (abs_nonneg _) _))
      (mul_nonneg (productMomentConstant_nonneg p) (pow_nonneg (scale_nonneg hR hE false) _))) hconst
  convert! hs using 1
  simp only [scale,Bool.false_eq_true,if_false]
  simp only [mul_pow]
  ring

end SHE.TwoFreshGaussianFractions
