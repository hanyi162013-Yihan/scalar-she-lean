module

public import SHE.FixedOldHessianBound
public import SHE.PhysicalScoreProduct
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.MeasurableGaussianScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianGramScore
open scoped InnerProductSpace BigOperators
variable {n r : ℕ}

theorem secondScore_absolute_mass {A : MeasurableGeneralizedInverse.Mat n} (hA : A.PosSemidef)
    {d : State n} (hd : d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) :
    (∫y,|secondScore A d y| ∂multivariateGaussian 0 A)≤2*scoreVariance A d := by
  let μ:=multivariateGaussian (0:State n) A
  have hV:=scoreVariance_nonneg hA hd
  have hi:Integrable (fun y=>firstScore A d y^2) μ:=
    (IsGaussian.memLp_dual μ (innerSL ℝ (coefficient A d)) 2 (by norm_num)).integrable_sq
  have he:(∫y,firstScore A d y^2 ∂μ)=scoreVariance A d:=by
    have hv:=firstScore_variance hA hd
    rw [variance_eq_integral (by fun_prop),gaussian_inner_mean_zero A (coefficient A d)] at hv
    simpa only [sub_zero,innerSL_apply_apply,firstScore] using hv
  have hb(y:State n):|secondScore A d y|≤firstScore A d y^2+scoreVariance A d:=by
    unfold secondScore
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg hV])
  have hs:Integrable (secondScore A d) μ:=GaussianVectorFractions.gaussian_secondScore_integrable A d
  calc
    _≤∫y,firstScore A d y^2+scoreVariance A d ∂μ:=integral_mono hs.abs (hi.add (integrable_const _)) hb
    _=2*scoreVariance A d:=by rw [integral_add hi (integrable_const _),he,integral_const];simp [μ];ring

theorem product_score_absolute_mass (A : Fin r→MeasurableGeneralizedInverse.Mat n)
    (hA : ∀j,(A j).PosSemidef) (d : Fin r→State n)
    (hd : ∀j,d j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range) :
    (∫y:Fin r→State n,|∏j,secondScore (A j) (d j) (y j)|
      ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))≤
        (2:ℝ)^r*(∏j,scoreVariance (A j) (d j)) := by
  simp_rw [Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod (μ:=fun j=>multivariateGaussian (0:State n) (A j))
    (fun j y=>|secondScore (A j) (d j) y|)]
  calc
    _≤∏j:Fin r,2*scoreVariance (A j) (d j):=
      Finset.prod_le_prod₀ (fun _ _=>integral_nonneg (fun _=>abs_nonneg _))
        (fun j _=>secondScore_absolute_mass (hA j) (hd j))
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end SHE.MeasurableGaussianScores

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers PhysicalScoreChain MeasurableGaussianScores ProjectedUncutWord
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ} (L : Level R X n)

theorem Chain.fixed_direction_mem_range {m N : ℕ} {p : History X m} {g : Fin (n+m)→Fin N}
    (chain : Chain L m p g) (j : Fin m) :
    chain.direction j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (chain.old j)).range:=by
  induction chain with
  | root p f=>exact Fin.elim0 j
  | step k p f g prev ht old residual ho hres hcov d hd hrg ih=>
    exact Fin.cases hrg (fun i=>ih i) j

/-- Fixed-old absolute mass is controlled by the already proved actual
old parent-score product, so its positive-gap spatial/time integrability
can be read from the physical forest envelope. -/
theorem oldAbsoluteMass_le_scoreProduct_ae (c : StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀p,ell≤c p ∧ c p≤R.reference p)
    (hages : ∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p∂CutoffWordHistories.historyMeasure R μ k,
      oldAbsoluteMass L c k p≤(2:ℝ)^k*
        PhysicalScoreChain.scoreProduct L ((carrier L k).observations.observations p) c k p := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,_,_,hphysical⟩:=hp
  have hr:=SHE.PhysicalChainArrays.Chain.fixed_direction_mem_range L chain
  have hh:=product_score_absolute_mass chain.old chain.old_posSemidef chain.direction hr
  rw [Physical.old_eq L _ c chain hphysical,Physical.direction_eq L _ c chain hphysical] at hh
  exact hh

end SHE.PhysicalChainArrays
