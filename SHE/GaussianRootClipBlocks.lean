module

public import SHE.GaussianAffineBlocks
public import SHE.GaussianRoughBlockMoments
public import SHE.GaussianClipProducts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.GaussianRootClipBlocks
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianRoughBlockMoments GaussianAffineBlocks
  GaussianClipMoments
open scoped BigOperators

theorem clips_map_eq_prod {I:Type*}(is:List I)(ν:ℝ)(x:I→ℝ):
    FiniteDifferences.clips ν (is.map x)=
      ∏j:Fin is.length,clip ν (x (is.get j)):=by
  have he:=congrArg (fun l:List I=>l.map (fun i=>clip ν (x i))) (List.ofFn_get is)
  simp only[List.map_ofFn] at he
  change ((is.map x).map (fun z=>min 1 (ν*|z|))).prod=_
  rw[List.map_map]
  change (is.map (fun i=>clip ν (x i))).prod=_
  rw[←he,Fin.prod_ofFn]
  rfl

/-- The exact canonical root block has all the original Bernstein clips.
Only a finite derivative packet up to its own block order is required. -/
theorem root_block_clipped_bound {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{n m:ℕ}
    (choices:List (Fin n×Fin m))(hnd:(choices.map Prod.fst).Nodup)(k:Fin m)
    (f:ℕ→ℝ→ℝ){A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν)
    (hf:∀j,j<(block choices k).length→∀z,HasDerivAt (f j) (f (j+1) z) z)
    (hfb:∀j,j≤(block choices k).length→∀z,|f j z|≤A0*ν^j)
    (mean:ℝ)(L:Fin n→V→L[ℝ] ℝ)(x:Fin n→V):
    |GaussianVectorFractions.fractionDifferences (block choices k) (fun y=>f 0 (affineSum mean L y))
      (suppress (suppressed choices k) x)|≤
      (2:ℝ)^((block choices k).length)*A0*
        (∏j:Fin (block choices k).length,clip ν (L ((block choices k).get j) (x ((block choices k).get j)))):=by
  rw[suppressed_block_eq_mixed choices hnd k]
  have hh:=FiniteDifferences.mixed_clipped_bound_finite f ((block choices k).length) hA0 hν hf hfb
    ((block choices k).map (fun i=>L i (x i))) 0 (by simp)
    (affineSum mean L (suppress (block choices k) (suppress (suppressed choices k) x)))
  simpa only[List.length_map,pow_zero,mul_one,clips_map_eq_prod] using hh

end SHE.GaussianRootClipBlocks
