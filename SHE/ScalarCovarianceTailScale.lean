module

public import SHE.CovarianceEndpoint
public import SHE.ProfileVariance
public import SHE.ControlledReferenceWindows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace SHE.ScalarCovarianceTailScale
open Set MeasureTheory Real StoppedFourier WordRecursion ProfileVariance
open scoped NNReal
local instance scalarCovarianceTailScale_period : Fact (0<2*π):=⟨by positivity⟩

def observation (b : ℝ) (x : HeatCircle) : Fin 1→Observation:=fun _=>⟨b,b,x⟩

/-- Exact remaining-window variance for the literal scalar covariance
used by the physical backward equation. -/
theorem diagonal_eq (c : (ℝ×HeatCircle)→ℝ) {q b : ℝ} (hqb : q≤b) (x : HeatCircle) :
    covariance c (observation b x) q b 0 0=
      varianceMap (fun p=>c (p.1+q,p.2)) (b-q) x := by
  have he:=intervalIntegral.integral_comp_add_right (a:=(0:ℝ)) (b:=b-q)
    (fun t=>covarianceDensity c (observation b x) t 0 0) q
  have ht : (∫ t in q..b,covarianceDensity c (observation b x) t 0 0)=
      ∫ t in (0:ℝ)..(b-q),covarianceDensity c (observation b x) (t+q) 0 0 := by
    simpa only [zero_add,sub_add_cancel] using he.symm
  rw [WordRecursion.covariance,ht,varianceMap]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (sub_nonneg.mpr hqb)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b-q))]
    with t ht hne
  have htb : t<b-q:=lt_of_le_of_ne ht.2 hne
  have hage : 0<b-(t+q):=by linarith
  unfold covarianceDensity varianceDensity
  apply integral_congr_ae
  filter_upwards with z
  simp only [heatRow,observation,WithLp.ofLp_toLp,show b-q-t=b-(t+q) by ring]
  rw [←WordRecursion.heatPhysical_real hage x z,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp only [Complex.ofReal_re]
  ring

/-- Actual uniformly elliptic future profiles give the required
sqrt(age) Gaussian variance, including arbitrary random-past sections. -/
theorem elliptic {c : (ℝ×HeatCircle)→ℝ} (hc : Measurable c) {q b m M : ℝ}
    (hqb : q<b) (hage : b-q≤1) (hm : 0≤m) (hM : 0≤M)
    (hb : ∀ p,m≤c p ∧ c p≤M) (x : HeatCircle) :
    lowerConstant*m*(b-q)^(1/2:ℝ)≤covariance c (observation b x) q b 0 0 ∧
      covariance c (observation b x) q b 0 0≤upperConstant*M*(b-q)^(1/2:ℝ) := by
  rw [diagonal_eq c hqb.le x]
  exact varianceMap_elliptic (hc.comp ((measurable_fst.add_const q).prodMk measurable_snd))
    (sub_pos.mpr hqb) hage hm hM (fun s hs z=>(hb (s+q,z)).1) (fun s hs z=>(hb (s+q,z)).2) x

end SHE.ScalarCovarianceTailScale
