module
public import SHE.PhysicalWordHessianMass
public import SHE.ScoreMixedMass

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalScoreChain.Physical OldIntervalCovariance StoppedGaussianFeatures
  GaussianConvolution MeasurableGaussianScores ProjectedUncutWord
open scoped BigOperators
local instance physicalFreshRowMass_period : Fact (0<2*Real.pi):=⟨by positivity⟩
attribute [local irreducible] fullResidualCovariance scoreVariance MeasurableGeneralizedInverse.generalizedInverse
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ} (L:Level R X n)

/-- Actual instantaneous fresh rows lie in the full residual range and
their full-residual score mass is bounded by the genuine fresh interval.
No AE future-time row is specialized to its time endpoint. -/
theorem fresh_row_score_mass_of_chain (c:Domain→ℝ)
    {ell:ℝ}(hell:0<ell)(hR:∀p,ell≤R.reference p)
    (hages:∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k:ℕ)(p:History X k)(chain:Chain L k p (fun i=>i))
    (hphysical:Physical L ((carrier L k).observations.observations p) c chain):
      ∀q:ℝ,0≤q→q<(carrier L k).terminal p→
      let T:=fullResidualCovariance L c k p q
      let row:=heatRow ((carrier L k).observations.observations p) q
      T.PosSemidef ∧
      (∀ᵐx:HeatCircle∂haarAddCircle,
        row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range ∧ 0≤scoreVariance T (row x)) ∧
      Integrable (fun x=>scoreVariance T (row x)) haarAddCircle ∧
      (∫x,scoreVariance T (row x) ∂haarAddCircle)≤
        ((n+k:ℕ):ℝ)/(ell*((carrier L k).terminal p-q)) := by
  intro q hq hqt
  dsimp only
  let Z:=(carrier L k).observations.observations p
  let hi:=(carrier L k).terminal p
  let C:=WordRecursion.covariance R.reference Z q hi
  let T:=fullResidualCovariance L c k p q
  let V:=fun x:HeatCircle=>scoreVariance T (heatRow Z q x)
  have hZ:∀i,(Z i).stop≤(Z i).target:=RecursiveScoreSupport.carrier_ages L hages k p
  have hstop:∀i,hi≤(Z i).stop:=(carrier L k).stops_after p
  have hcb:∀p,ell≤R.reference p ∧ R.reference p≤R.upper:=
    fun p=>⟨hR p,(le_abs_self _).trans (R.reference_bound p)⟩
  have heC:intervalCovariance Z R.reference q hi=C:=
    PhysicalIntervalCovariance.interval_eq_covariance Z R.reference R.reference_measurable R.reference_bound
      hZ hstop hq hqt.le
  have hC:C.PosSemidef:=by
    rw [←heC]
    exact PhysicalFirstScore.interval_posSemidef Z hZ R.reference R.reference_measurable
      (fun p=>⟨R.reference_nonneg p,(hcb p).2⟩) q hi
  have hTC:(T-C).PosSemidef:=by
    change (fullResidualCovariance L c k p q-WordRecursion.covariance R.reference Z q hi).PosSemidef
    unfold fullResidualCovariance
    rw [add_sub_cancel_left,←Physical.residual_eq L Z c chain hphysical]
    exact Matrix.posSemidef_sum _ (fun j _=>chain.residual_posSemidef j)
  have hT:T.PosSemidef:=by
    have hh:=hC.add hTC
    convert! hh using 1 <;> abel
  have hr:=endpoint_row_mem_range_unrestricted (fun i=>(Z i).stop) (fun i=>(Z i).target)
    (fun i=>(Z i).center) hZ hq hqt (fun i=>Or.inr (hstop i))
      R.reference R.reference_measurable hell hcb
  have hmass:=IntervalScoreMass.score_mass_bound (fun i=>(Z i).stop) (fun i=>(Z i).target)
    (fun i=>(Z i).center) hZ R.reference R.reference_measurable hq hqt
      (fun i=>Or.inr (hstop i)) hell hcb
  have hrow (x:HeatCircle):stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>(Z i).center) (q,x)=heatRow Z q x:=by
    ext i
    simp only [stoppedRow,heatRow,ite_eq_left (hqt.trans_le (hstop i))]
  simp only [hrow] at hr hmass
  change ∀ᵐx:HeatCircle∂haarAddCircle,
    heatRow Z q x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z R.reference q hi)).range at hr
  rw [heC] at hr
  change Integrable (fun x:HeatCircle=>scoreVariance (intervalCovariance Z R.reference q hi)
    (heatRow Z q x)) haarAddCircle ∧
    (∫x:HeatCircle,scoreVariance (intervalCovariance Z R.reference q hi) (heatRow Z q x) ∂haarAddCircle)≤
      ((n+k:ℕ):ℝ)/(ell*(hi-q)) at hmass
  rw [heC] at hmass
  have hbound:∀ᵐx:HeatCircle∂haarAddCircle,
      heatRow Z q x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range ∧
      0≤V x ∧ V x≤scoreVariance C (heatRow Z q x):=by
    filter_upwards [hr] with x hx
    have ht:heatRow Z q x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range:=
      PositiveMatrixRanges.range_le_of_domination hT hC 1 (by simpa only [one_smul] using hTC) hx
    exact ⟨ht,scoreVariance_nonneg hT ht,scoreVariance_antitone_matrix hC hT hTC hx⟩
  have hVm:Measurable V:=scoreVariance_measurable.comp (measurable_const.prodMk
    ((HeatRowWeighted.heatRow_vector_measurable Z).comp (measurable_const.prodMk measurable_id)))
  have hVi:Integrable V haarAddCircle:=hmass.1.mono' hVm.aestronglyMeasurable
    (hbound.mono (fun x hx=>by rw [Real.norm_of_nonneg hx.2.1];exact hx.2.2))
  exact ⟨hT,hbound.mono (fun _ hx=>⟨hx.1,hx.2.1⟩),hVi,
    (integral_mono_ae hVi hmass.1 (hbound.mono (fun _ hx=>hx.2.2))).trans hmass.2⟩

theorem actual_fresh_row_score_mass_ae (c:Domain→ℝ)(hc:Measurable c)
    {ell:ℝ}(hell:0<ell)(hb:∀p,ell≤c p ∧ c p≤R.reference p)
    (hages:∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ:Measure X)[IsFiniteMeasure μ](k:ℕ):
    ∀ᵐp∂CutoffWordHistories.historyMeasure R μ k,
      ∀q:ℝ,0≤q→q<(carrier L k).terminal p→
      let T:=fullResidualCovariance L c k p q
      let row:=heatRow ((carrier L k).observations.observations p) q
      T.PosSemidef ∧
      (∀ᵐx:HeatCircle∂haarAddCircle,
        row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range ∧ 0≤scoreVariance T (row x)) ∧
      Integrable (fun x=>scoreVariance T (row x)) haarAddCircle ∧
      (∫x,scoreVariance T (row x) ∂haarAddCircle)≤
        ((n+k:ℕ):ℝ)/(ell*((carrier L k).terminal p-q)) := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hs
  obtain ⟨chain,_,_,hphysical⟩:=hs
  exact fresh_row_score_mass_of_chain L c hell (fun p=>(hb p).1.trans (hb p).2)
    hages k p chain hphysical

end SHE.PhysicalChainArrays
