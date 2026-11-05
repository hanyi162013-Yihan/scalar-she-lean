module

public import SHE.StoppedRowWeighted
public import SHE.GaussianIncrement
public import SHE.ProfileVariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Exact scalar marginals of the full individually stopped covariance.
A native coordinate has its own physical variance of order sqrt(target),
regardless of the other target ages and observation collisions. -/
namespace SHE.StoppedGaussianMarginals
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  StoppedGaussianFeatures StoppedRowWeighted ProfileVariance GaussianIncrement WordRecursion
open scoped InnerProductSpace
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n:ℕ}

theorem native_covariance_diagonal (target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (ht:∀i,0<target i)(ht1:∀i,target i≤1)
    (c:Domain→ℝ)(hc:Measurable c)(M:ℝ)(hcb:∀p,0≤c p ∧ c p≤M)(i:Fin n):
    StoppedGaussianFeatures.stoppedCovariance target target center c 0 i i=
      varianceMap c (target i) (center i):=by
  let f:Domain→ℝ:=fun p=>‖heatPhysical (target i-p.1) (center i) p.2‖^2*c p
  let S:Set Domain:=(Ioc 0 (target i))×ˢ(univ:Set HeatCircle)
  have hSm:MeasurableSet S:=measurableSet_Ioc.prod MeasurableSet.univ
  have ht0:∀ᵐp:Domain ∂historyMeasure 0,0<p.1:=by
    have hh:∀ᵐt:ℝ ∂volume.restrict (Ici 0),0<t:=by
      filter_upwards[ae_restrict_mem measurableSet_Ici,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with t ht hn
      exact lt_of_le_of_ne ht hn.symm
    exact Measure.quasiMeasurePreserving_fst.ae hh
  have htne:∀ᵐp:Domain ∂historyMeasure 0,p.1≠target i:=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae (volume.ae_ne (target i)))
  have heq:(fun p:Domain=>c p*stoppedRow target target center p i^2)=ᵐ[historyMeasure 0] S.indicator f:=by
    filter_upwards[ht0,htne] with p hp hn
    by_cases hpi:p.1<target i
    · have hmem:p∈S:=⟨⟨hp,hpi.le⟩,mem_univ _⟩
      rw[Set.indicator_of_mem hmem]
      change c p*(if p.1<target i then (heatPhysical (target i-p.1) (center i) p.2).re else 0)^2=f p
      rw[ite_eq_left hpi]
      dsimp only[f]
      rw[←heatPhysical_real (sub_pos.mpr hpi)]
      simp only[Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.ofReal_re]
      ring
    · have hmem:p∉S:=by intro hh;exact hpi (lt_of_le_of_ne hh.1.2 hn)
      rw[Set.indicator_of_notMem hmem]
      change c p*(if p.1<target i then (heatPhysical (target i-p.1) (center i) p.2).re else 0)^2=0
      simp[hpi]
  have hentry:Integrable (fun p:Domain=>stoppedRow target target center p i^2) (historyMeasure 0):=by
    simpa only[Real.rpow_zero,one_mul] using
      weighted_stopped_entry_integrable target target center ht ht1 (fun _=>le_rfl) (by norm_num:(-1:ℝ)<0) i
  have hg:Integrable (fun p:Domain=>c p*stoppedRow target target center p i^2) (historyMeasure 0):=
    hentry.bdd_mul hc.aestronglyMeasurable (ae_of_all _ (fun p=>by
      rw[Real.norm_eq_abs,abs_of_nonneg (hcb p).1];exact (hcb p).2))
  have hfi:Integrable f (HeatRowWeighted.sourceMeasure (target i)):=by
    have hindi:=hg.congr heq
    have hh:IntegrableOn f S (historyMeasure 0):=(integrable_indicator_iff hSm).mp hindi
    change Integrable f ((historyMeasure 0).restrict S) at hh
    rwa[historyMeasure_restrict_stop] at hh
  calc
    _=∫p,c p*stoppedRow target target center p i^2 ∂historyMeasure 0:=by
      unfold StoppedGaussianFeatures.stoppedCovariance
      congr 1;funext p;ring
    _=∫p,S.indicator f p ∂historyMeasure 0:=integral_congr_ae heq
    _=∫p,f p ∂HeatRowWeighted.sourceMeasure (target i):=by
      rw[integral_indicator hSm]
      rw[historyMeasure_restrict_stop]
    _=varianceMap c (target i) (center i):=by
      rw[HeatRowWeighted.sourceMeasure,integral_prod _ hfi]
      rw[varianceMap,intervalIntegral.integral_of_le (ht i).le]
      rfl

/-- The scalar Gaussian leaf marginal retains its own sqrt-age variance
scale, even if other observations have much older targets. -/
theorem native_coordinate_variance_bound (target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (ht:∀i,0<target i)(ht1:∀i,target i≤1)
    (c:Domain→ℝ)(hc:Measurable c)(M:ℝ)(hcb:∀p,0≤c p ∧ c p≤M)(i:Fin n):
    Var[EuclideanSpace.proj (𝕜:=ℝ) i;
      multivariateGaussian 0 (StoppedGaussianFeatures.stoppedCovariance target target center c 0)]≤
      upperConstant*M*(target i)^(1/2:ℝ):=by
  have hM:0≤M:=(hcb (0,0)).1.trans (hcb (0,0)).2
  have hA:(StoppedGaussianFeatures.stoppedCovariance target target center c 0).PosSemidef:=by
    rw[←weightedFeature_gram target target center c hc M hcb (fun _=>le_rfl) 0]
    exact Matrix.posSemidef_gram ℝ _
  rw[show Var[EuclideanSpace.proj (𝕜:=ℝ) i;
      multivariateGaussian 0 (StoppedGaussianFeatures.stoppedCovariance target target center c 0)]=
      StoppedGaussianFeatures.stoppedCovariance target target center c 0 i i by
        exact variance_eval_multivariateGaussian hA i]
  rw[native_covariance_diagonal target center ht ht1 c hc M hcb i]
  exact (varianceMap_elliptic hc (ht i) (ht1 i) (by norm_num:0≤(0:ℝ)) hM
    (fun s _ y=>(hcb (s,y)).1) (fun s _ y=>(hcb (s,y)).2) (center i)).2

end SHE.StoppedGaussianMarginals
