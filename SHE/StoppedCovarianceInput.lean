module

public import SHE.GaussianWordCovarianceBound
public import SHE.StoppedScoreLeverage
public import SHE.StoppedProfileMark

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Actual signed covariance-profile inputs against the complete stopped
canonical score kernel. The coarse pointwise time power justifies all
integrals; no inverse-conditioning constant enters the final bound. -/
namespace SHE.StoppedCovarianceInput
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  StoppedScoreLeverage StoppedProfileMark StoppedRowWeighted GaussianProfileMark
  GaussianIncrement GaussianWordCovarianceIntegral GaussianWordCovarianceBound
  MeasurableGaussianScores
open scoped InnerProductSpace
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {n:ℕ}

theorem row_mem_covariance_range_ae
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)
    (hages:∀i,σ i≤target i)(c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)
    (hcb:∀p,0≤c p ∧ c p≤U)(hell:0<ell)(hcl:∀p,ell≤c p):
    ∀ᵐp ∂historyMeasure 0,stoppedRow σ target center p∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c 0)).range:=by
  have hi:=bounded_profile_frame_integrable σ target center hσ hσ1 hages (by norm_num:0≤(0:ℝ))
    hc (fun p=>by rw[abs_of_nonneg (hcb p).1];exact (hcb p).2)
  have hh:=ae_frame_mem_profile_range (historyMeasure 0) (stoppedRow σ target center)
    (stoppedRow_measurable σ target center).aestronglyMeasurable
    (row_energy_integrable σ target center hages 0) c hc.aestronglyMeasurable hi hell (ae_of_all _ hcl)
  rw[profileCovariance_eq_stopped σ target center hσ hσ1 hages (by norm_num:0≤(0:ℝ)) hc
    (fun p=>by rw[abs_of_nonneg (hcb p).1];exact (hcb p).2)] at hh
  exact hh

theorem weighted_input_energy_integrable
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)
    (hages:∀i,σ i≤target i)(e:Domain→ℝ)(he:Measurable e){E τ:ℝ}
    (hτ:-1<τ)(hdom:∀p,0≤p.1→|e p|≤E*p.1^τ):
    Integrable (fun p=>|e p| *‖stoppedRow σ target center p‖^2) (historyMeasure 0):=by
  have hi:=weighted_stopped_row_integrable σ target center hσ hσ1 hages hτ
  apply (hi.const_mul E).mono'
    (((continuous_abs.measurable.comp he).mul ((stoppedRow_measurable σ target center).norm.pow_const 2)).aestronglyMeasurable)
  have ht:∀ᵐp:Domain ∂historyMeasure 0,0≤p.1:=Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  filter_upwards[ht] with p hp
  change ‖|e p| *‖stoppedRow σ target center p‖^2‖≤_
  rw[Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  convert! mul_le_mul_of_nonneg_right (hdom p hp) (sq_nonneg ‖stoppedRow σ target center p‖) using 1
  ring

/-- Integrating the signed physical input against the canonical score
energy gives the exact negative-power leverage rate of the earliest stop. -/
theorem score_input_weighted_bound
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)
    (hages:∀i,σ i≤target i){s τ E:ℝ}(hs:0<s)(hτ:-1<τ)(hτ0:τ<0)
    (hE:0≤E)(hstop:∀i,s≤σ i)(c:Domain→ℝ)(hc:Measurable c)(U ell:ℝ)
    (hcb:∀p,0≤c p ∧ c p≤U)(hell:0<ell)(hcl:∀p,ell≤c p)
    (e:Domain→ℝ)(he:Measurable e)(hdom:∀p,0≤p.1→|e p|≤E*p.1^τ):
    Integrable (fun p=>|e p| *scoreVariance (stoppedCovariance σ target center c 0)
      (stoppedRow σ target center p)) (historyMeasure 0) ∧
    (∫p,|e p| *scoreVariance (stoppedCovariance σ target center c 0)
      (stoppedRow σ target center p) ∂historyMeasure 0)≤
      E*((n:ℝ)/ell)*(s/2)^τ*(1+2/(τ+1)):=by
  let A:=stoppedCovariance σ target center c 0
  let v:=stoppedRow σ target center
  have henergy:=weighted_input_energy_integrable σ target center hσ hσ1 hages e he hτ hdom
  have hi:=scoreEnergy_outer_integrable (historyMeasure 0) A v (stoppedRow_measurable σ target center) e he henergy
  have hrange:=row_mem_covariance_range_ae σ target center hσ hσ1 hages c hc U ell hcb hell hcl
  have href:=referenceKernel_weighted_mass σ target center hages hs hτ hτ0 hstop
  have hdomScore:=score_le_reference_ae σ target center hages c hc U hcb hell hcl 0
  have ht:∀ᵐp:Domain ∂historyMeasure 0,0≤p.1:=Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  have hb:∀ᵐp ∂historyMeasure 0,|e p| *scoreVariance A (v p)≤
      (E/ell)*(p.1^τ*referenceKernel σ target center hages 0 p):=by
    filter_upwards[hdomScore,hrange,ht] with p hp hr ht
    have hK0:0≤referenceKernel σ target center hages 0 p:=
      (GaussianAudit.physicalLeverage_properties (referenceCoefficients σ target center hages 0)
        σ target center hages).2.1 p
    calc
      _≤|e p| *(referenceKernel σ target center hages 0 p/ell):=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _≤(E*p.1^τ)*(referenceKernel σ target center hages 0 p/ell):=
        mul_le_mul_of_nonneg_right (hdom p ht) (div_nonneg hK0 hell.le)
      _=_:=by ring
  refine ⟨hi,(integral_mono_ae hi (href.1.const_mul (E/ell)) hb).trans ?_⟩
  rw[integral_const_mul]
  convert! mul_le_mul_of_nonneg_left href.2 (div_nonneg hE hell.le) using 1
  ring

end SHE.StoppedCovarianceInput
