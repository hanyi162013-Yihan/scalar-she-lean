module

public import SHE.HeatSpanHaarMass

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.HeatProjection
open MeasureTheory Set Real AddCircle HeatTorus HeatTorusKernel FiniteHaar
  GaussianGramScore GaussianIncrement RealHeatCovarianceMean MeasurableGaussianScores
local instance heatSpanSignedHaarMass_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- The bounded slot in the quadratic defect may itself be the signed
matched Haar factor. This rank bound does not spend the signed smallness
which is retained in the other slot. -/
theorem bounded_signed_haar_projection_mass {q:ℕ}(t:Fin q→ℝ)(a:Fin q→UnitAddCircle)
    (f g:CircleHeat.CircleL2)(m U:ℝ)(hm:0<m)
    (hfreal:∀ᵐy∂haarAddCircle,(f y).im=0)(hgreal:∀ᵐy∂haarAddCircle,(g y).im=0)
    (hf:∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤U)
    (hg:∀ᵐy∂haarAddCircle,m≤(g y).re ∧ (g y).re≤U):
    Summable (fun j:HaarNode=>‖(heatSpan t a).starProjection (globalSignedColumn j f g)‖^2) ∧
      (∑'j:HaarNode,‖(heatSpan t a).starProjection (globalSignedColumn j f g)‖^2)≤4*U*(q:ℝ):=by
  have h1:=bounded_haar_projection_mass t a f m U hm hfreal hf
  have h2:=bounded_haar_projection_mass t a g m U hm hgreal hg
  have hp(j:HaarNode):‖(heatSpan t a).starProjection (globalSignedColumn j f g)‖^2≤
      2*‖(heatSpan t a).starProjection (globalHaarColumn j f)‖^2+
        2*‖(heatSpan t a).starProjection (globalHaarColumn j g)‖^2:=by
    rw [globalSignedColumn,map_sub]
    have hn:=norm_sub_le ((heatSpan t a).starProjection (globalHaarColumn j f))
      ((heatSpan t a).starProjection (globalHaarColumn j g))
    have hs:=sq_nonneg (‖(heatSpan t a).starProjection (globalHaarColumn j f)‖-
      ‖(heatSpan t a).starProjection (globalHaarColumn j g)‖)
    nlinarith [norm_nonneg ((heatSpan t a).starProjection (globalHaarColumn j f)),
      norm_nonneg ((heatSpan t a).starProjection (globalHaarColumn j g)),
      norm_nonneg ((heatSpan t a).starProjection (globalHaarColumn j f)-
        (heatSpan t a).starProjection (globalHaarColumn j g))]
  have hs:Summable (fun j:HaarNode=>2*‖(heatSpan t a).starProjection (globalHaarColumn j f)‖^2+
      2*‖(heatSpan t a).starProjection (globalHaarColumn j g)‖^2):=
    (h1.1.mul_left 2).add (h2.1.mul_left 2)
  have ht:Summable (fun j:HaarNode=>‖(heatSpan t a).starProjection (globalSignedColumn j f g)‖^2):=
    Summable.of_nonneg_of_le (fun j=>sq_nonneg _) hp hs
  refine ⟨ht,?_⟩
  have hh:=ht.tsum_le_tsum hp hs
  rw [Summable.tsum_add (h1.1.mul_left 2) (h2.1.mul_left 2),tsum_mul_left,tsum_mul_left] at hh
  nlinarith [h1.2,h2.2]

theorem bounded_signed_haar_score_mass {q n:ℕ}{G:Type*}[NormedAddCommGroup G]
    [InnerProductSpace ℝ G][CompleteSpace G]
    (t:Fin q→ℝ)(a:Fin q→UnitAddCircle)(S:State n→ₗ[ℝ]CircleHeat.CircleL2)
    (v:Fin n→G)(hspan:∀z,S z∈heatSpan t a){L:ℝ}(hL:0≤L)
    (hbound:∀z,‖S z‖≤L*‖featureSynthesis v z‖)
    (f g:CircleHeat.CircleL2)(m U:ℝ)(hm:0<m)
    (hfreal:∀ᵐy∂haarAddCircle,(f y).im=0)(hgreal:∀ᵐy∂haarAddCircle,(g y).im=0)
    (hf:∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤U)
    (hg:∀ᵐy∂haarAddCircle,m≤(g y).re ∧ (g y).re≤U):
    Summable (fun j:HaarNode=>scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalSignedColumn j f g))) ∧
    (∑'j:HaarNode,scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalSignedColumn j f g)))≤L^2*(4*U*(q:ℝ)):=by
  have hp:=bounded_signed_haar_projection_mass t a f g m U hm hfreal hgreal hf hg
  have hscore(j:HaarNode):=scoreVariance_projection_bound t a S v hspan hL hbound (globalSignedColumn j f g)
  have hn(j:HaarNode):0≤scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalSignedColumn j f g)):=
    scoreVariance_nonneg (Matrix.posSemidef_gram ℝ v) (hscore j).1
  have hs:Summable (fun j:HaarNode=>scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalSignedColumn j f g))):=
    Summable.of_nonneg_of_le hn (fun j=>(hscore j).2) (hp.1.mul_left (L^2))
  refine ⟨hs,?_⟩
  calc
    _≤∑'j:HaarNode,L^2*‖(heatSpan t a).starProjection (globalSignedColumn j f g)‖^2:=
      hs.tsum_le_tsum (fun j=>(hscore j).2) (hp.1.mul_left (L^2))
    _=L^2*(∑'j:HaarNode,‖(heatSpan t a).starProjection (globalSignedColumn j f g)‖^2):=tsum_mul_left
    _≤L^2*(4*U*(q:ℝ)):=mul_le_mul_of_nonneg_left hp.2 (sq_nonneg _)

end SHE.HeatProjection
