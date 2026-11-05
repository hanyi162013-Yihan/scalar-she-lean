module

public import SHE.GaussianRoughBlocks
public import SHE.GaussianEnvelopeMoments
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.GaussianRoughBlockMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianVectorFractions GaussianAssignmentBlocks GaussianRoughBlocks GaussianEnvelopeMoments
open scoped NNReal InnerProductSpace BigOperators

def blockFunction {d n m:ℕ}(choices:List (Fin n×Fin m))(k:Fin m)(a:ℝ→ℝ)
    (mean:ℝ)(L:Fin n→State d→L[ℝ] ℝ)(x:Fin n→State d):ℝ:=
  GaussianVectorFractions.fractionDifferences (block choices k) (fun y=>a (affineSum mean L y))
    (suppress (suppressed choices k) x)

theorem blockFunction_measurable {d n m:ℕ}(choices:List (Fin n×Fin m))(k:Fin m)(a:ℝ→ℝ)
    (ha:Measurable a)(mean:ℝ)(L:Fin n→State d→L[ℝ] ℝ):Measurable (blockFunction choices k a mean L):=by
  have hs:Measurable (fun x:Fin n→State d=>affineSum mean L x):=by
    dsimp[affineSum]
    fun_prop
  have hm:Measurable (fun x:Fin n→State d=>a (affineSum mean L x)):=ha.comp hs
  exact (GaussianVectorFractions.measurable_fractionDifferences _ _ hm).comp (measurable_suppress _)

theorem selected_projection_hasLaw {d n:ℕ}(A:Fin n→Matrix (Fin d) (Fin d) ℝ)
    (L:Fin n→State d→L[ℝ] ℝ)(i:Fin n):
    HasLaw (fun x:Fin n→State d=>L i (x i))
      (gaussianReal 0 (Var[L i;multivariateGaussian 0 (A i)]).toNNReal)
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))):=by
  let μ:=fun j=>multivariateGaussian (0:State d) (A j)
  have h0:(∫y,L i y ∂μ i)=0:=by
    have hh:=(L i).integral_comp_comm (IsGaussian.integrable_id (μ:=μ i))
    simpa only[μ,id_eq,integral_id_multivariateGaussian,map_zero] using hh
  have hLi:=projection_hasLaw (μ i) (L i) h0
  have heval:HasLaw (fun x:Fin n→State d=>x i) (μ i) (Measure.pi μ):=
    ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval μ i).map_eq⟩
  exact hLi.fun_comp heval

/-- The selected assigned increment is integrated under its actual full
vector Gaussian marginal. Neither the base mean nor any other increment
is separated from the rough block. -/
theorem block_even_moment {d n m:ℕ}(A:Fin n→Matrix (Fin d) (Fin d) ℝ)
    (choices:List (Fin n×Fin m))(hnd:(choices.map Prod.fst).Nodup)(k:Fin m)(i:Fin n)
    (hi:i∈block choices k)(a:ℝ→ℝ)(ha:Measurable a){H β:ℝ}(hH:0≤H)(hβ:0≤β)
    (hholder:∀z w,|a z-a w|≤H*|z-w|^β)(mean:ℝ)(L:Fin n→State d→L[ℝ] ℝ)(p:ℕ):
    Integrable (fun x=>|blockFunction choices k a mean L x|^(2*p))
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))) ∧
    (∫x,|blockFunction choices k a mean L x|^(2*p) ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))≤
      gaussianAbsMoment (((2*p:ℕ):ℝ)*β)*
        ((2:ℝ)^((block choices k).length-1)*H*Var[L i;multivariateGaussian 0 (A i)]^(β/2))^(2*p):=by
  have hb:∀x:Fin n→State d,|blockFunction choices k a mean L x|≤
      ((2:ℝ)^((block choices k).length-1)*H)*|L i (x i)|^β:=
    fun x=>suppressed_rough_block_bound choices hnd k i hi a H β hholder mean L x
  have hh:=dominated_even_moment (Measure.pi (fun j=>multivariateGaussian 0 (A j)))
    (fun x:Fin n→State d=>L i (x i)) (blockFunction choices k a mean L)
    (selected_projection_hasLaw A L i) (blockFunction_measurable choices k a ha mean L)
    (show 0≤(2:ℝ)^((block choices k).length-1)*H by positivity) hβ hb p
  simpa only[Real.coe_toNNReal _ (variance_nonneg (L i) (multivariateGaussian (0:State d) (A i)))] using hh

end SHE.GaussianRoughBlockMoments
