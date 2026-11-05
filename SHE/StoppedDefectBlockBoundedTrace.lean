module

public import SHE.StoppedDefectBlockProjection
public import SHE.HeatSpanSignedHaarMass
public import SHE.StoppedCovarianceSplit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.StoppedDefectBlockBoundedTrace
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores BlockDefectScores StoppedDefectBlockProjection
local instance stoppedDefectBlockBoundedTrace_period:Fact (0<2*π):=⟨by positivity⟩

/-- In the quadratic defect the second signed factor can be bounded
without losing the negative-input smallness retained in the first slot.
All scores use the ORIGINAL full stopped covariance. -/
theorem trace {n g:ℕ}(hg:0<g)(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (hrep:∀j,label (rep j)=j)(σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)(hΛ:0<Λ)
    (t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)(hages:∀i,σ i≤target i)
    (lower upper M:Fin g→ℝ)(A:ℝ)(hA:4*(g:ℝ)^2+1≤A)
    (hlo:∀j,0<lower j)(hlohi:∀j,lower j≤upper j)(hM:∀j,1≤M j)
    (hratio:∀j,upper j≤M j*lower j)
    (hstlo:∀i,u+lower (label i)≤σ i)(hsthi:∀i,σ i≤u+upper (label i))
    (hsep:∀j k,j<k→A*upper j≤lower k)
    (c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)(hcb:∀p,0≤c p ∧ c p≤U)
    (hell:0<ell)(hcl:∀p,ell≤c p)(j:Fin g)
    (f g0:CircleHeat.CircleL2)(m W:ℝ)(hm:0<m)
    (hfreal:∀ᵐy∂haarAddCircle,(f y).im=0)(hgreal:∀ᵐy∂haarAddCircle,(g0 y).im=0)
    (hf:∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤W)
    (hg0:∀ᵐy∂haarAddCircle,m≤(g0 y).re ∧ (g0 y).re≤W):
    let act:∀j i,u<groupData label rep σ j i:=fun j i=>by
      have hp:=(groupData_bounds label rep hrep σ (fun j=>u+lower j)
        (fun j=>u+upper j) hstlo hsthi j i).1
      linarith [hlo j]
    let S:=synthesis label rep σ target a u Λ t hage act j
    let V:=stoppedCovariance σ target (nativeCenter a) c u
    (∀l:HaarNode,meanDirection S (globalSignedColumn l f g0)∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) V).range) ∧
    Summable (fun l:HaarNode=>scoreVariance V (meanDirection S (globalSignedColumn l f g0))) ∧
    (∑'l:HaarNode,scoreVariance V (meanDirection S (globalSignedColumn l f g0)))≤
      ((max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2))*(4*W*(n:ℝ)):=by
  intro act S V
  let E:=(max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2)
  have hE:0≤E:=div_nonneg (mul_nonneg
    (mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) (sq_nonneg _))
    (inv_nonneg.mpr (hlo j).le)) (half_pos hell).le
  have hp:=bounded_signed_haar_projection_mass (groupData label rep t j)
    (groupData label rep a j) f g0 m W hm hfreal hgreal hf hg0
  have hscore(l:HaarNode):meanDirection S (globalSignedColumn l f g0)∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) V).range ∧
      scoreVariance V (meanDirection S (globalSignedColumn l f g0))≤
        E*‖(heatSpan (groupData label rep t j) (groupData label rep a j)).starProjection
          (globalSignedColumn l f g0)‖^2:=
    score_projection hg label rep hrep σ target a u Λ hΛ t hage hages lower upper M A hA
      hlo hlohi hM hratio hstlo hsthi hsep c hc U ell hcb hell hcl j (globalSignedColumn l f g0)
  have hV:V.PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target (nativeCenter a)
    hages u hc hcb
  have hn(l:HaarNode):0≤scoreVariance V (meanDirection S (globalSignedColumn l f g0)):=
    scoreVariance_nonneg hV (hscore l).1
  have hs:Summable (fun l:HaarNode=>scoreVariance V (meanDirection S (globalSignedColumn l f g0))):=
    Summable.of_nonneg_of_le hn (fun l=>(hscore l).2) (hp.1.mul_left E)
  refine ⟨fun l=>(hscore l).1,hs,?_⟩
  calc
    _≤∑'l:HaarNode,E*‖(heatSpan (groupData label rep t j) (groupData label rep a j)).starProjection
        (globalSignedColumn l f g0)‖^2:=hs.tsum_le_tsum (fun l=>(hscore l).2) (hp.1.mul_left E)
    _=E*(∑'l:HaarNode,‖(heatSpan (groupData label rep t j) (groupData label rep a j)).starProjection
        (globalSignedColumn l f g0)‖^2):=tsum_mul_left
    _≤E*(4*W*(n:ℝ)):=mul_le_mul_of_nonneg_left hp.2 hE

end SHE.StoppedDefectBlockBoundedTrace
