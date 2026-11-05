module

public import SHE.GaussianRootClipBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.GaussianRootBlockMoments
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAudit
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianRoughBlockMoments GaussianRootClipBlocks
  GaussianClipMoments GaussianClipProducts
open scoped NNReal InnerProductSpace BigOperators

/-- All clips of the actual canonical old root block survive high moments.
Each original projected increment may be correlated with its own score
and with every rough factor in the word. -/
theorem root_block_even_moment {d n m:ℕ}(A:Fin n→Matrix (Fin d) (Fin d) ℝ)
    (choices:List (Fin n×Fin m))(hnd:(choices.map Prod.fst).Nodup)(k:Fin m)
    (hlen:0<(block choices k).length)(f:ℕ→ℝ→ℝ){A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν)
    (hf:∀j,j<(block choices k).length→∀z,HasDerivAt (f j) (f (j+1) z) z)
    (hfb:∀j,j≤(block choices k).length→∀z,|f j z|≤A0*ν^j)
    (mean:ℝ)(L:Fin n→State d→L[ℝ] ℝ)(p:ℕ):
    Integrable (fun y=>|blockFunction choices k (f 0) mean L y|^(2*p))
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))) ∧
    (∫y,|blockFunction choices k (f 0) mean L y|^(2*p) ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))≤
      clipMomentConstant (p*(block choices k).length)*
        ((2:ℝ)^((block choices k).length)*A0*
          (∏j:Fin (block choices k).length,min 1
            (ν*sqrt (Var[L ((block choices k).get j);
              multivariateGaussian 0 (A ((block choices k).get j))]))))^(2*p):=by
  let is:=block choices k
  let X:=fun (j:Fin is.length) (y:Fin n→State d)=>L (is.get j) (y (is.get j))
  let v:=fun j:Fin is.length=>(Var[L (is.get j);multivariateGaussian 0 (A (is.get j))]).toNNReal
  have hX:∀j,HasLaw (X j) (gaussianReal 0 (v j)) (Measure.pi (fun i=>multivariateGaussian 0 (A i))):=
    fun j=>selected_projection_hasLaw A L (is.get j)
  have hXm:∀j,Measurable (X j):=fun j=>(L (is.get j)).continuous.measurable.comp (measurable_pi_apply (is.get j))
  have hfc:Measurable (f 0):=(continuous_iff_continuousAt.mpr (fun z=>(hf 0 hlen z).continuousAt)).measurable
  have hR:Measurable (blockFunction choices k (f 0) mean L):=blockFunction_measurable choices k (f 0) hfc mean L
  have hb (y:Fin n→State d):|blockFunction choices k (f 0) mean L y|≤
      ((2:ℝ)^is.length*A0)*(∏j,clip ν (X j y)):=
    root_block_clipped_bound choices hnd k f hA0 hν hf hfb mean L y
  have hh:=GaussianClipProducts.dominated_even_moment (Measure.pi (fun j=>multivariateGaussian 0 (A j)))
    hlen X hXm v hX hν (show 0≤(2:ℝ)^is.length*A0 by positivity)
    _ hR hb p
  have hv (j:Fin is.length):((v j:ℝ))=Var[L (is.get j);multivariateGaussian 0 (A (is.get j))]:=
    Real.coe_toNNReal _ (variance_nonneg _ _)
  simpa only[hv] using hh

end SHE.GaussianRootBlockMoments
