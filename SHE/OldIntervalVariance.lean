module

public import SHE.OldIntervalGaussian
public import SHE.StoppedRowWeighted
public import SHE.StoppedGaussianMarginals

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

/-! The selected Gaussian block gains the true old interval length,
uniformly over all original observation targets and centers. -/
namespace SHE.OldIntervalVariance
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement
  OldIntervalCovariance StoppedGaussianFeatures StoppedRowWeighted StoppedFourier ProfileVariance
  WordRecursion
open scoped NNReal InnerProductSpace
local instance : Fact (0<2*π):=⟨by positivity⟩

theorem window_power_integrable {lo hi:ℝ}(_hgap:lo<hi):
    IntervalIntegrable (fun t:ℝ=>(hi-t)^(-(1/2:ℝ))) volume lo hi:=by
  have hh:IntervalIntegrable (fun t:ℝ=>t^(-(1/2:ℝ))) volume 0 (hi-lo):=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  convert! (hh.comp_sub_left hi).symm using 1 <;> ring

theorem window_power_mass {lo hi:ℝ}(_hgap:lo<hi):
    (∫t in lo..hi,(hi-t)^(-(1/2:ℝ)))=2*(hi-lo)^(1/2:ℝ):=by
  rw[intervalIntegral.integral_comp_sub_left (fun t:ℝ=>t^(-(1/2:ℝ))) hi,sub_self]
  rw[integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2:ℝ)))]
  norm_num[Real.zero_rpow (by norm_num:(1/2:ℝ)≠0)]
  ring

theorem covariance_diagonal_eq_interval {n:ℕ}(σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (c:Domain→ℝ){lo hi:ℝ}(hlo:0≤lo)(i:Fin n):
    stoppedCovariance σ target center (intervalProfile c lo hi) 0 i i=
      ∫p,c p*stoppedRow σ target center p i^2 ∂intervalMeasure lo hi:=by
  unfold StoppedGaussianFeatures.stoppedCovariance
  have he:(fun p:Domain=>intervalProfile c lo hi p*stoppedRow σ target center p i*stoppedRow σ target center p i)=
      (timeSet lo hi).indicator (fun p=>c p*stoppedRow σ target center p i^2):=by
    funext p
    by_cases hp:p∈timeSet lo hi
    · simp only[intervalProfile,Set.indicator_of_mem hp];ring
    · simp only[intervalProfile,Set.indicator_of_notMem hp,zero_mul]
  have hS:MeasurableSet (timeSet lo hi):=measurableSet_Ioc.prod MeasurableSet.univ
  rw[he,integral_indicator hS,←intervalMeasure_eq_restrict hlo]

theorem covariance_diagonal_bound {n:ℕ}(σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)(hages:∀i,σ i≤target i)
    (c:Domain→ℝ)(hc:Measurable c){M lo hi:ℝ}(hcb:∀p,0≤c p ∧ c p≤M)
    (hlo:0≤lo)(hgap:lo<hi)(hstop:∀i,σ i≤lo ∨ hi≤σ i)(i:Fin n):
    stoppedCovariance σ target center (intervalProfile c lo hi) 0 i i≤upperConstant*M*(hi-lo)^(1/2:ℝ):=by
  have hM:0≤M:=(hcb (0,0)).1.trans (hcb (0,0)).2
  rcases hstop i with hinactive|hactive
  · rw[covariance_inactive_row σ target center c lo hi i i hinactive]
    exact mul_nonneg (mul_nonneg upperConstant_pos.le hM) (rpow_nonneg (sub_pos.mpr hgap).le _)
  let f:=fun p:Domain=>c p*stoppedRow σ target center p i^2
  have hi0:Integrable (fun p:Domain=>stoppedRow σ target center p i^2) (historyMeasure 0):=by
    simpa only[Real.rpow_zero,one_mul] using
      weighted_stopped_entry_integrable σ target center hσ hσ1 hages (by norm_num:(-1:ℝ)<0) i
  have hfi0:Integrable f (historyMeasure 0):=hi0.bdd_mul hc.aestronglyMeasurable (ae_of_all _ (fun p=>by
    rw[Real.norm_eq_abs,abs_of_nonneg (hcb p).1]
    exact (hcb p).2))
  have hfi:Integrable f (intervalMeasure lo hi):=by
    rw[intervalMeasure_eq_restrict hlo]
    exact hfi0.mono_measure Measure.restrict_le_self
  have his:Integrable (fun t=>∫y,f (t,y) ∂haarAddCircle) (volume.restrict (Ioc lo hi)):=hfi.integral_prod_left
  have hp:=window_power_integrable hgap
  have hupper:Integrable (fun t:ℝ=>M*(1+heatConstant)*(hi-t)^(-(1/2:ℝ))) (volume.restrict (Ioc lo hi)):=
    hp.1.const_mul _
  have hbound:∀ᵐt ∂volume.restrict (Ioc lo hi),(∫y,f (t,y) ∂haarAddCircle)≤M*(1+heatConstant)*(hi-t)^(-(1/2:ℝ)):=by
    filter_upwards[ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne hi)] with t ht hne
    have hthi:t<hi:=lt_of_le_of_ne ht.2 hne
    have hts:t<σ i:=hthi.trans_le hactive
    have htt:t<target i:=hts.trans_le (hages i)
    have he:(∫y,f (t,y) ∂haarAddCircle)=varianceDensity c (target i) (center i) t:=by
      apply integral_congr_ae
      exact ae_of_all _ (fun y=>by
        dsimp[f,varianceDensity,stoppedRow]
        rw[ite_eq_left hts,←heatPhysical_real (sub_pos.mpr htt)]
        simp only[Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,sq_abs]
        ring)
    rw[he]
    have hv:=varianceDensity_bound hc hM htt (fun y=>by
      rw[abs_of_nonneg (hcb (t,y)).1];exact (hcb (t,y)).2) (center i)
    have hmass:=circleHeat_norm_sq_bound (sub_pos.mpr htt) (center i)
    have hpow:((target i)-t)^(-(1/2:ℝ))≤(hi-t)^(-(1/2:ℝ)):=
      rpow_le_rpow_of_nonpos (sub_pos.mpr hthi) (by linarith[hages i]) (by norm_num)
    have hone:1≤(hi-t)^(-(1/2:ℝ)):=one_le_rpow_of_pos_of_le_one_of_nonpos
      (sub_pos.mpr hthi) (by linarith[ht.1,hσ1 i]) (by norm_num)
    have hmass':‖circleHeat (target i-t) (center i)‖^2≤(1+heatConstant)*(hi-t)^(-(1/2:ℝ)):=by
      nlinarith[mul_le_mul_of_nonneg_left hpow heatConstant_pos.le]
    exact (le_abs_self _).trans (hv.trans (by convert! mul_le_mul_of_nonneg_left hmass' hM using 1;ring))
  rw[covariance_diagonal_eq_interval σ target center c hlo i,intervalMeasure,integral_prod _ hfi]
  have hb:=integral_mono_ae his hupper hbound
  have he:(∫t,M*(1+heatConstant)*(hi-t)^(-(1/2:ℝ)) ∂volume.restrict (Ioc lo hi))=
      upperConstant*M*(hi-lo)^(1/2:ℝ):=by
    rw[←intervalIntegral.integral_of_le hgap.le,intervalIntegral.integral_const_mul,window_power_mass hgap]
    unfold upperConstant
    ring
  exact hb.trans_eq he

theorem coordinate_variance_bound {n:ℕ}(σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)(hages:∀i,σ i≤target i)
    (c:Domain→ℝ)(hc:Measurable c){M lo hi:ℝ}(hcb:∀p,0≤c p ∧ c p≤M)
    (hlo:0≤lo)(hgap:lo<hi)(hstop:∀i,σ i≤lo ∨ hi≤σ i)(i:Fin n):
    Var[EuclideanSpace.proj (𝕜:=ℝ) i;
      multivariateGaussian 0 (stoppedCovariance σ target center (intervalProfile c lo hi) 0)]≤
        upperConstant*M*(hi-lo)^(1/2:ℝ):=by
  rw[show Var[EuclideanSpace.proj (𝕜:=ℝ) i;
      multivariateGaussian 0 (stoppedCovariance σ target center (intervalProfile c lo hi) 0)]=
        stoppedCovariance σ target center (intervalProfile c lo hi) 0 i i by
    exact variance_eval_multivariateGaussian (covariance_posSemidef σ target center hages c hc hcb lo hi) i]
  exact covariance_diagonal_bound σ target center hσ hσ1 hages c hc hcb hlo hgap hstop i

end SHE.OldIntervalVariance
