module

public import SHE.StoppedBlockDefectEnergy
public import SHE.StoppedDefectMeanEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.StoppedDefectBlockProjection
open Set MeasureTheory Real AddCircle StoppedFourier StoppedGaussianFeatures StoppedGaussianScore
  StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores BlockDefectScores
local instance stoppedDefectBlockProjection_period:Fact (0<2*π):=⟨by positivity⟩

def synthesis {n g:ℕ}(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)
    (t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀j i,u<groupData label rep σ j i)(j:Fin g):State n→ₗ[ℝ]HeatTorus.CircleL2:=
  (((heatSpan (groupData label rep t j) (groupData label rep a j)).subtype).restrictScalars ℝ).comp
    (defectBlockRow label rep σ target a u Λ t hage act j)

/-- A selected age block is normalized by the ORIGINAL full weighted
stopped covariance. Other original coordinates are retained in its Gram
frame; there is no contracted or reduced covariance law. -/
theorem score_projection {n g:ℕ}(hg:0<g)(label:Fin n→Fin g)(rep:Fin g→Fin n)
    (hrep:∀j,label (rep j)=j)(σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)(hΛ:0<Λ)
    (t:Fin n→ℝ)(hage:∀i,target i-u=4*π^2*t i)(hages:∀i,σ i≤target i)
    (lower upper M:Fin g→ℝ)(A:ℝ)(hA:4*(g:ℝ)^2+1≤A)
    (hlo:∀j,0<lower j)(hlohi:∀j,lower j≤upper j)(hM:∀j,1≤M j)
    (hratio:∀j,upper j≤M j*lower j)
    (hstlo:∀i,u+lower (label i)≤σ i)(hsthi:∀i,σ i≤u+upper (label i))
    (hsep:∀j k,j<k→A*upper j≤lower k)
    (c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)(hcb:∀p,0≤c p ∧ c p≤U)
    (hell:0<ell)(hcl:∀p,ell≤c p)(j:Fin g)(d:HeatTorus.CircleL2):
    let act:∀j i,u<groupData label rep σ j i:=fun j i=>by
      have hp:=(groupData_bounds label rep hrep σ (fun j=>u+lower j) (fun j=>u+upper j) hstlo hsthi j i).1
      linarith [hlo j]
    let S:=synthesis label rep σ target a u Λ t hage act j
    let V:=stoppedCovariance σ target (nativeCenter a) c u
    meanDirection S d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) V).range ∧
      scoreVariance V (meanDirection S d)≤
        (max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹)/(ell/2)*
          ‖(heatSpan (groupData label rep t j) (groupData label rep a j)).starProjection d‖^2:=by
  intro act S V
  let v:=weightedFeature σ target (nativeCenter a) c hc U hcb hages u
  let C:=StoppedAgeBlocks.blockSynthesis label rep σ target (nativeCenter a) hages u
  let E:=max (M j) 8*min 1 (Λ*lower j)^2*(lower j)⁻¹
  have hE:0≤E:=by
    dsimp [E]
    exact mul_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) (sq_nonneg _))
      (inv_nonneg.mpr (hlo j).le)
  have hframe(z:State n):(ell/2)*(∑k,‖C k z‖^2)≤‖featureSynthesis v z‖^2:=
    weighted_block_frame hg label rep hrep σ target (nativeCenter a) hages u lower upper A
      hA hlo hlohi hstlo hsthi hsep c hc U ell hcb hell.le hcl z
  have hspan(z:State n):S z∈heatSpan (groupData label rep t j) (groupData label rep a j):=
    (defectBlockRow label rep σ target a u Λ t hage act j z).property
  have hrow(z:State n):‖S z‖≤sqrt (E/(ell/2))*‖featureSynthesis v z‖:=by
    have hd:‖S z‖^2≤E*‖C j z‖^2:=by
      exact defectBlockRow_energy label rep σ target a u Λ hΛ t hage hages act j
        (lower j) (M j) (hlo j) (hM j)
        (fun i=>(groupData_bounds label rep hrep σ (fun j=>u+lower j) (fun j=>u+upper j) hstlo hsthi j i).1)
        (fun i=>by
          have hi:=(groupData_bounds label rep hrep σ (fun j=>u+lower j) (fun j=>u+upper j) hstlo hsthi j i).2
          linarith [hratio j]) z
    have hs:‖C j z‖^2≤∑k:Fin g,‖C k z‖^2:=
      Finset.single_le_sum (f:=fun k:Fin g=>‖C k z‖^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ j)
    have hdom:=(mul_le_mul_of_nonneg_left hs (half_pos hell).le).trans (hframe z)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,sq_sqrt (div_nonneg hE (half_pos hell).le)]
    calc
      _≤E*‖C j z‖^2:=hd
      _=(E/(ell/2))*((ell/2)*‖C j z‖^2):=by field_simp
      _≤_:=mul_le_mul_of_nonneg_left hdom (div_nonneg hE (half_pos hell).le)
  have hh:=scoreVariance_projection_bound (groupData label rep t j) (groupData label rep a j)
    S v hspan (sqrt_nonneg _) hrow d
  rw [sq_sqrt (div_nonneg hE (half_pos hell).le),weightedFeature_gram] at hh
  exact hh

end SHE.StoppedDefectBlockProjection
