module
public import SHE.PhysicalFreshRowMass
public import SHE.FullFutureScoreOrder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.AllProfileInstantScoreMass
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  OldIntervalCovariance MeasurableGaussianScores GaussianIncrement
open scoped BigOperators
local instance allProfileInstantScoreMass_period : Fact (0<2*π):=⟨by positivity⟩
variable {ι:Type*}{n:ℕ}
attribute [local irreducible] StoppedGaussianFeatures.stoppedCovariance
  MeasurableGaussianScores.scoreVariance MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse

def reference (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(ell q:ℝ)(y:HeatCircle):ℝ:=
  scoreVariance (stoppedCovariance σ target center (fun _=>ell) q)
    (stoppedRow σ target center (q,y))

/-- A single deterministic reference score mass dominates every
bounded elliptic full future profile simultaneously at the exact fresh
time. The input circle event is selected before any random profile. -/
theorem all_profiles (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hages:∀i,σ i≤target i){q hi ell M:ℝ}(hq:0≤q)(hgap:q<hi)
    (hstop:∀i,hi≤σ i)(hell:0<ell)
    (c:ι→Domain→ℝ)(hc:∀a,Measurable (c a))(hb:∀a p,ell≤c a p ∧ c a p≤M):
    Integrable (reference σ target center ell q) haarAddCircle ∧
    (∫y,reference σ target center ell q y ∂haarAddCircle)≤(n:ℝ)/(ell*(hi-q)) ∧
    ∀ᵐy:HeatCircle∂haarAddCircle,0≤reference σ target center ell q y ∧
      ∀a,stoppedRow σ target center (q,y)∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
          (stoppedCovariance σ target center (c a) q)).range ∧
        0≤scoreVariance (stoppedCovariance σ target center (c a) q) (stoppedRow σ target center (q,y)) ∧
        scoreVariance (stoppedCovariance σ target center (c a) q) (stoppedRow σ target center (q,y))≤
          reference σ target center ell q y := by
  let A:=stoppedCovariance σ target center (intervalProfile (fun _=>ell) q hi) 0
  let T:=stoppedCovariance σ target center (fun _=>ell) q
  let row:=fun y:HeatCircle=>stoppedRow σ target center (q,y)
  have hA:A.PosSemidef:=covariance_posSemidef σ target center hages (fun _=>ell) measurable_const
    (fun _=>⟨hell.le,le_rfl⟩) q hi
  have hT:T.PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target center hages q
    measurable_const (fun _=>⟨hell.le,le_rfl⟩)
  have heA:stoppedCovariance σ target center (intervalProfile (fun _=>ell) q hi) q=A:=
    FutureWindowDomination.interval_covariance_eq σ target center (fun _=>ell) hq le_rfl
  have hwin(p:Domain):0 ≤ intervalProfile (fun _=>ell) q hi p ∧
      intervalProfile (fun _=>ell) q hi p≤ell:=by
    by_cases hp:p∈OldIntervalCovariance.timeSet q hi
    · simpa only [intervalProfile,indicator_of_mem hp] using
        (show 0≤ell ∧ ell≤ell from ⟨hell.le,le_rfl⟩)
    · simpa only [intervalProfile,indicator_of_notMem hp] using
        (show 0≤(0:ℝ) ∧ 0≤ell from ⟨le_rfl,hell.le⟩)
  have hAT:(T-A).PosSemidef:=by
    rw [←heA]
    exact StoppedCovarianceOrder.covariance_sub_posSemidef σ target center hages q _ _
      (measurable_intervalProfile measurable_const q hi) measurable_const hwin
      (fun _=>⟨hell.le,le_rfl⟩) (fun p=>(hwin p).2)
  have hr:=endpoint_row_mem_range_unrestricted σ target center hages hq hgap
    (fun i=>Or.inr (hstop i)) (fun _=>ell) measurable_const hell (fun _=>⟨le_rfl,le_rfl⟩)
  have hm:=IntervalScoreMass.score_mass_bound σ target center hages (fun _=>ell) measurable_const
    hq hgap (fun i=>Or.inr (hstop i)) hell (fun _=>⟨le_rfl,le_rfl⟩)
  have hbound:∀ᵐy:HeatCircle∂haarAddCircle,
      row y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range ∧
        0≤reference σ target center ell q y ∧
        reference σ target center ell q y≤scoreVariance A (row y):=by
    filter_upwards [hr] with y hy
    have ht:row y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range:=
      PositiveMatrixRanges.range_le_of_domination hT hA 1 (by simpa only [one_smul] using hAT) hy
    exact ⟨ht,scoreVariance_nonneg hT ht,scoreVariance_antitone_matrix hA hT hAT hy⟩
  have hVm:Measurable (reference σ target center ell q):=scoreVariance_measurable.comp
    (measurable_const.prodMk ((stoppedRow_measurable σ target center).comp
      (measurable_const.prodMk measurable_id)))
  have hVi:Integrable (reference σ target center ell q) haarAddCircle:=hm.1.mono' hVm.aestronglyMeasurable
    (hbound.mono (fun y hy=>by rw [Real.norm_of_nonneg hy.2.1];exact hy.2.2))
  refine ⟨hVi,(integral_mono_ae hVi hm.1 (hbound.mono (fun _ h=>h.2.2))).trans hm.2,?_⟩
  filter_upwards [hbound] with y hy
  refine ⟨hy.2.1,fun a=>?_⟩
  have hR:=StoppedCovarianceOrder.range_mono σ target center hages q (fun _=>ell) (c a)
    measurable_const (hc a) (fun _=>⟨hell.le,le_rfl⟩)
    (fun p=>⟨hell.le.trans (hb a p).1,(hb a p).2⟩) (fun p=>(hb a p).1) hy.1
  have hC: (stoppedCovariance σ target center (c a) q).PosSemidef:=
    StoppedCovarianceSplit.covariance_posSemidef σ target center hages q (hc a)
      (fun p=>⟨hell.le.trans (hb a p).1,(hb a p).2⟩)
  exact ⟨hR,scoreVariance_nonneg hC hR,
    StoppedCovarianceOrder.scoreVariance_antitone σ target center hages q (fun _=>ell) (c a)
      measurable_const (hc a) (fun _=>⟨hell.le,le_rfl⟩)
      (fun p=>⟨hell.le.trans (hb a p).1,(hb a p).2⟩) (fun p=>(hb a p).1) hy.1⟩

end SHE.AllProfileInstantScoreMass
