module

public import SHE.GaussianScoreQuadratic
public import SHE.GaussianScoreKernel
public import SHE.TwoFreshBoundedHaarContraction
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SHE.FiniteHaarScoreTrace
open Set MeasureTheory ProbabilityTheory Real FiniteHaar GaussianIncrement MeasurableGaussianScores
open scoped BigOperators

/-- The canonical score remains quadratic on a singular covariance
range. Finite age blocks are combined in that SAME full range. -/
theorem sum_variance {n g:ℕ}(A:Matrix (Fin n) (Fin n) ℝ)(hA:A.PosSemidef)
    (D:Fin g→State n)(hD:∀i,D i∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range):
    scoreVariance A (∑i,D i)≤(g:ℝ)*(∑i,scoreVariance A (D i)):=by
  let μ:=multivariateGaussian (0:State n) A
  have hd:(∑i,D i)∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range:=
    Submodule.sum_mem _ (fun i _=>hD i)
  have moments(d:State n)(hd:d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range):
      Integrable (fun y=>firstScore A d y^2) μ ∧
        (∫y,firstScore A d y^2 ∂μ)=scoreVariance A d:=by
    have hh:=firstScore_even_moments hA hd 1
    simpa only [Nat.mul_one,pow_one,GaussianScoreKernel.firstScoreMoment_one,mul_one,sq_abs] using hh
  have hp(y:State n):firstScore A (∑i,D i) y^2≤(g:ℝ)*(∑i,firstScore A (D i) y^2):=by
    have hh:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i:Fin g=>firstScore A (D i) y)
    simpa only [firstScore,coefficient,map_sum,sum_inner,Finset.card_univ,Fintype.card_fin] using hh
  have hi:Integrable (fun y=>∑i,firstScore A (D i) y^2) μ:=
    integrable_finset_sum _ (fun i _=>(moments (D i) (hD i)).1)
  have hh:=integral_mono (moments _ hd).1 (hi.const_mul g) hp
  rw [(moments _ hd).2,integral_const_mul,integral_finsetSum _ (fun i _=>(moments (D i) (hD i)).1)] at hh
  simpa only [(moments _ (hD _)).2] using hh

/-- Full original Haar score traces can be bounded before selecting
any measurable age partition. Each genuine block retains its own trace. -/
theorem trace {n g:ℕ}(A:Matrix (Fin n) (Fin n) ℝ)(hA:A.PosSemidef)
    (D:Fin g→HaarNode→State n)
    (hD:∀i l,D i l∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (hs:∀i,Summable (fun l:HaarNode=>scoreVariance A (D i l))):
    (∀l:HaarNode,(∑i,D i l)∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) ∧
      Summable (fun l:HaarNode=>scoreVariance A (∑i,D i l)) ∧
      (∑'l:HaarNode,scoreVariance A (∑i,D i l))≤
        (g:ℝ)*(∑i,∑'l:HaarNode,scoreVariance A (D i l)):=by
  have hr(l:HaarNode):(∑i,D i l)∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range:=
    Submodule.sum_mem _ (fun i _=>hD i l)
  have hn(l:HaarNode):0≤scoreVariance A (∑i,D i l):=scoreVariance_nonneg hA (hr l)
  have hb(l:HaarNode):scoreVariance A (∑i,D i l)≤
      (g:ℝ)*(∑i,scoreVariance A (D i l)):=sum_variance A hA _ (fun i=>hD i l)
  have hsmajor:Summable (fun l:HaarNode=>(g:ℝ)*(∑i,scoreVariance A (D i l))):=
    (summable_sum (fun i _=>hs i)).mul_left (g:ℝ)
  have hi:Summable (fun l:HaarNode=>scoreVariance A (∑i,D i l)):=
    Summable.of_nonneg_of_le hn hb hsmajor
  refine ⟨hr,hi,(hi.tsum_le_tsum hb hsmajor).trans_eq ?_⟩
  rw [tsum_mul_left,Summable.tsum_finsetSum (fun i _=>hs i)]

end SHE.FiniteHaarScoreTrace
