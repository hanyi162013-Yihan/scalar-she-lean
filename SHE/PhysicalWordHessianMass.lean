module

public import SHE.PhysicalWordHessianCap
public import SHE.GaussianMatrixScoreOrder
public import SHE.IntervalScoreMass
public import SHE.PhysicalIntervalCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain OldIntervalCovariance
open StoppedGaussianFeatures GaussianConvolution MeasurableGaussianScores SmoothCylinders
local instance physicalWordHessianMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] fullResidualCovariance oldAverage WordRecursion.covariance
  MeasurableGaussianScores.scoreVariance MeasurableGeneralizedInverse.generalizedInverse
  WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ} (L : Level R X n)

/-- Genuine spatial Hessian mass of the actual finite word. The fresh
inverse covariance is dominated by the true current window. This cap
uses only zeroth coefficient bounds and the fixed-old geometric mass. -/
theorem actual_hessian_mass_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell ellR A B : ℝ} (hell : 0<ell) (hb : ∀p,ell≤c p ∧ c p≤R.reference p)
    (hellR : 0<ellR) (hR : ∀p,ellR≤R.reference p)
    (hA : 0≤A) (hB : 0≤B) (ha : ∀z,|R.totalVariance z|≤A)
    (hroot : ∀p z,|L.test p z|≤B)
    (hages : ∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p∂CutoffWordHistories.historyMeasure R μ k,
      ∀q:ℝ,0≤q→q<(carrier L k).terminal p→∀z:WordRecursion.State (n+k),
      Integrable (fun x:HeatCircle=>WordRecursion.directionalSecond
        (gaussianAverage (WordRecursion.covariance R.reference
          ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
            (UncutSmoothWords.test L k p)) z
              (heatRow ((carrier L k).observations.observations p) q x)) haarAddCircle ∧
      (∫x:HeatCircle,|WordRecursion.directionalSecond
        (gaussianAverage (WordRecursion.covariance R.reference
          ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
            (UncutSmoothWords.test L k p)) z
              (heatRow ((carrier L k).observations.observations p) q x)| ∂haarAddCircle)≤
        (2*((B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p))*
          ((n+k:ℕ):ℝ)/(ellR*((carrier L k).terminal p-q)) := by
  filter_upwards [actual_hessian_cap_ae L c hc hell hb hA hB ha hroot hages μ k,
    exists_chain_ae L c hc hell hb hages μ k] with p hp hs
  obtain ⟨chain,hchain,_,hphysical⟩:=hs
  intro q hq hqt z
  let Z:=(carrier L k).observations.observations p
  let hi:=(carrier L k).terminal p
  let C:=WordRecursion.covariance R.reference Z q hi
  let T:=fullResidualCovariance L c k p q
  let K:=(B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p
  have hK:0≤K:=mul_nonneg
    (mul_nonneg hB (pow_nonneg (div_nonneg (add_nonneg hA R.upper_nonneg) (by norm_num)) _))
      (oldAbsoluteMass_nonneg L c k p)
  have hZ:∀i,(Z i).stop≤(Z i).target:=RecursiveScoreSupport.carrier_ages L hages k p
  have hstop:∀i,hi≤(Z i).stop:=(carrier L k).stops_after p
  have hcb:∀p,ellR≤R.reference p ∧ R.reference p≤R.upper:=
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
      R.reference R.reference_measurable hellR hcb
  have hmass:=IntervalScoreMass.score_mass_bound (fun i=>(Z i).stop) (fun i=>(Z i).target)
    (fun i=>(Z i).center) hZ R.reference R.reference_measurable hq hqt
      (fun i=>Or.inr (hstop i)) hellR hcb
  have hrow (x:HeatCircle):stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>(Z i).center) (q,x)=heatRow Z q x:=by
    ext i
    simp only [stoppedRow,heatRow,ite_eq_left (hqt.trans_le (hstop i))]
  simp only [hrow] at hr hmass
  change ∀ᵐ x:HeatCircle∂haarAddCircle,
    heatRow Z q x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance Z R.reference q hi)).range at hr
  rw [heC] at hr
  change Integrable (fun x:HeatCircle=>scoreVariance (intervalCovariance Z R.reference q hi)
    (heatRow Z q x)) haarAddCircle ∧
    (∫x:HeatCircle,scoreVariance (intervalCovariance Z R.reference q hi) (heatRow Z q x) ∂haarAddCircle)≤
      ((n+k:ℕ):ℝ)/(ellR*(hi-q)) at hmass
  rw [heC] at hmass
  have hbound:∀ᵐ x:HeatCircle∂haarAddCircle,
      |WordRecursion.directionalSecond (gaussianAverage C (UncutSmoothWords.test L k p)) z (heatRow Z q x)|≤
        2*K*scoreVariance C (heatRow Z q x):=by
    filter_upwards [hr] with x hx
    have ht:heatRow Z q x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range:=
      PositiveMatrixRanges.range_le_of_domination hT hC 1 (by simpa only [one_smul] using hTC) hx
    exact (hp q hq hqt _ z ht).trans
      (mul_le_mul_of_nonneg_left (scoreVariance_antitone_matrix hC hT hTC hx) (mul_nonneg (by norm_num) hK))
  have hm:Measurable (fun x:HeatCircle=>WordRecursion.directionalSecond
      (gaussianAverage C (UncutSmoothWords.test L k p)) z (heatRow Z q x)):=by
    unfold WordRecursion.directionalSecond
    have hr:Measurable (fun x:HeatCircle=>heatRow Z q x):=
      (HeatRowWeighted.heatRow_vector_measurable Z).comp (measurable_const.prodMk measurable_id)
    have he₁:Continuous (fun p:(WordRecursion.State (n+k)→L[ℝ]WordRecursion.State (n+k)→L[ℝ]ℝ)×WordRecursion.State (n+k)=>p.1 p.2):=
      continuous_fst.clm_apply continuous_snd
    have he₂:Continuous (fun p:(WordRecursion.State (n+k)→L[ℝ]ℝ)×WordRecursion.State (n+k)=>p.1 p.2):=
      continuous_fst.clm_apply continuous_snd
    exact he₂.measurable.comp ((he₁.measurable.comp
      ((measurable_const (a:=WordRecursion.hessian (gaussianAverage C (UncutSmoothWords.test L k p)) z)).prodMk hr)).prodMk hr)
  have hiFun:Integrable (fun x:HeatCircle=>WordRecursion.directionalSecond
      (gaussianAverage C (UncutSmoothWords.test L k p)) z (heatRow Z q x)) haarAddCircle:=
    (hmass.1.const_mul (2*K)).mono' hm.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hiFun,?_⟩
  calc
    _≤∫x:HeatCircle,2*K*scoreVariance C (heatRow Z q x) ∂haarAddCircle:=
      integral_mono_ae hiFun.norm (hmass.1.const_mul _) hbound
    _=2*K*(∫x:HeatCircle,scoreVariance C (heatRow Z q x) ∂haarAddCircle):=integral_const_mul _ _
    _≤2*K*(((n+k:ℕ):ℝ)/(ellR*(hi-q))):=mul_le_mul_of_nonneg_left hmass.2 (by positivity)
    _=_:=by ring

end SHE.PhysicalChainArrays
