module

public import SHE.StoppedDefectBlockProjection
public import SHE.HeatSpanHaarMass
public import SHE.StoppedMeanRange

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace SHE.StoppedCurrentBlockHaarTrace
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores StoppedMeanRange
local instance stoppedCurrentBlockHaarTrace_period:Fact (0<2*π):=⟨by positivity⟩

def synthesis {n g:ℕ}(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u:ℝ)
    (t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀j i,u<groupData label rep σ j i)(j:Fin g):State n→ₗ[ℝ]HeatTorus.CircleL2:=
  (currentSynthesis (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep a j) u (groupData label rep t j)
    (fun i=>by unfold groupData;split_ifs <;>exact hage _) (act j)).comp
      (restrictCoefficients label j)

theorem basis {n g:ℕ}(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u:ℝ)
    (t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀j i,u<groupData label rep σ j i)(j:Fin g)(i:Fin n):
    synthesis label rep σ target a u t hage act j (EuclideanSpace.basisFun (Fin n) ℝ i)=
      if label i=j then unitHeatKernel (t i) (a i) else 0:=by
  unfold synthesis
  rw [LinearMap.comp_apply,restrictCoefficients_basis]
  by_cases hi:label i=j
  · rw [if_pos hi,if_pos hi,currentSynthesis_basis]
    simp only [groupData,hi,ite_true]
  · rw [if_neg hi,if_neg hi,map_zero]

/-- The bounded companion SAME-Haar factor pays only the original
block's inverse stopping age and the finite observed heat-span rank.
It is scored against the full original covariance. -/
theorem trace {n g:ℕ}(hg:0<g)(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (hrep:∀j,label (rep j)=j)(σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u:ℝ)
    (t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)(hages:∀i,σ i≤target i)
    (lower upper:Fin g→ℝ)(A:ℝ)(hA:4*(g:ℝ)^2+1≤A)
    (hlo:∀j,0<lower j)(hlohi:∀j,lower j≤upper j)
    (hstlo:∀i,u+lower (label i)≤σ i)(hsthi:∀i,σ i≤u+upper (label i))
    (hsep:∀j k,j<k→A*upper j≤lower k)
    (c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)(hcb:∀p,0≤c p ∧ c p≤U)
    (hell:0<ell)(hcl:∀p,ell≤c p)(j:Fin g)
    (f:CircleHeat.CircleL2)(m W:ℝ)(hm:0<m)
    (hfreal:∀ᵐy∂haarAddCircle,(f y).im=0)
    (hf:∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤W):
    let act:∀j i,u<groupData label rep σ j i:=fun j i=>by
      have hp:=(groupData_bounds label rep hrep σ (fun j=>u+lower j)
        (fun j=>u+upper j) hstlo hsthi j i).1
      linarith [hlo j]
    let S:=synthesis label rep σ target a u t hage act j
    let V:=stoppedCovariance σ target (nativeCenter a) c u
    (∀l:HaarNode,meanDirection S (globalHaarColumn l f)∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) V).range) ∧
    Summable (fun l:HaarNode=>scoreVariance V (meanDirection S (globalHaarColumn l f))) ∧
    (∑'l:HaarNode,scoreVariance V (meanDirection S (globalHaarColumn l f)))≤
      ((2/lower j)/(ell/2))*W*(n:ℝ):=by
  intro act S V
  let v:=weightedFeature σ target (nativeCenter a) c hc U hcb hages u
  let C:=StoppedAgeBlocks.blockSynthesis label rep σ target (nativeCenter a) hages u
  let L:=sqrt ((2/lower j)/(ell/2))
  have hcoef:0≤(2/lower j)/(ell/2):=
    div_nonneg (div_nonneg (by norm_num) (hlo j).le) (half_pos hell).le
  have hspan(z:State n):S z∈heatSpan (groupData label rep t j) (groupData label rep a j):=
    (realCurrent (groupData label rep σ j) (groupData label rep target j)
      (groupData label rep a j) u (groupData label rep t j)
      (fun i=>by unfold groupData;split_ifs <;>exact hage _) (act j)
      (restrictCoefficients label j z)).property
  have hframe(z:State n):(ell/2)*(∑k,‖C k z‖^2)≤‖featureSynthesis v z‖^2:=
    weighted_block_frame hg label rep hrep σ target (nativeCenter a) hages u lower upper A
      hA hlo hlohi hstlo hsthi hsep c hc U ell hcb hell.le hcl z
  have hrow(z:State n):‖S z‖≤L*‖featureSynthesis v z‖:=by
    have he:=stopped_current_row_bound Finset.univ
      (fun i=>((restrictCoefficients label j z) i:ℂ))
      (groupData label rep σ j) (groupData label rep target j)
      (nativeCenter (groupData label rep a j))
      (fun i _=>groupData_ages label rep σ target hages j i) (hlo j)
      (fun i _=>(groupData_bounds label rep hrep σ (fun j=>u+lower j)
        (fun j=>u+upper j) hstlo hsthi j i).1)
    have hcenter:nativeCenter (groupData label rep a j)=groupData label rep (nativeCenter a) j:=by
      funext i;unfold nativeCenter groupData;split_ifs <;>rfl
    rw [hcenter] at he
    have hs:‖S z‖^2≤(2/lower j)*‖C j z‖^2:=by
      rw [StoppedAgeBlocks.blockSynthesis_norm_sq]
      change ‖currentHeatRow (groupData label rep σ j) (groupData label rep target j)
        (groupData label rep a j) u (groupData label rep t j)
        (fun i=>by unfold groupData;split_ifs <;>exact hage _) (act j)
        (fun i=>((restrictCoefficients label j z) i:ℂ))‖^2≤_
      rw [currentHeatRow_norm_sq]
      change ‖historyF Finset.univ (fun i=>((restrictCoefficients label j z) i:ℂ))
        (groupData label rep σ j) (groupData label rep target j)
        (nativeCenter (groupData label rep a j)) u‖^2≤_
      rw [hcenter]
      exact he
    have hsingle:‖C j z‖^2≤∑k:Fin g,‖C k z‖^2:=
      Finset.single_le_sum (f:=fun k:Fin g=>‖C k z‖^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ j)
    have hd:=(mul_le_mul_of_nonneg_left hsingle (half_pos hell).le).trans (hframe z)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,sq_sqrt hcoef]
    calc
      _≤(2/lower j)*‖C j z‖^2:=hs
      _=((2/lower j)/(ell/2))*((ell/2)*‖C j z‖^2):=by field_simp
      _≤_:=mul_le_mul_of_nonneg_left hd hcoef
  have hh:=bounded_haar_score_mass (groupData label rep t j) (groupData label rep a j)
    S v hspan (sqrt_nonneg _) hrow f m W hm hfreal hf
  have hr(l:HaarNode):=scoreVariance_projection_bound (groupData label rep t j)
    (groupData label rep a j) S v hspan (sqrt_nonneg _) hrow (globalHaarColumn l f)
  have hgram:Matrix.gram ℝ v=V:=weightedFeature_gram σ target (nativeCenter a) c hc U hcb hages u
  rw [hgram] at hh
  simp_rw [hgram] at hr
  refine ⟨fun l=>(hr l).1,hh.1,?_⟩
  simpa only [L,sq_sqrt hcoef] using hh.2

end SHE.StoppedCurrentBlockHaarTrace
