module

public import SHE.NativeOldFraction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Exact positive old-fraction covariance splitting for native targets
(h,s), with the newest reserve retaining the original full history. -/
namespace SHE.NativeOldSplit
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  ProfileVariance OldFractionHeatScale NativeWordTimeFields NativeOldFraction
  StoppedGaussianMarginals GaussianIncrement GaussianGramScore
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

private theorem targets_positive {h s:ℝ}(hs:0<s)(hsh:s<h)(i:Fin 2):0<targets h s i:=by
  classical
  by_cases hi:i=0 <;> simp only[targets,hi,ite_true,ite_false] <;> linarith

private theorem targets_le_one {h s:ℝ}(hsh:s<h)(hh:h≤1)(i:Fin 2):targets h s i≤1:=by
  classical
  by_cases hi:i=0 <;> simp only[targets,hi,ite_true,ite_false] <;> linarith

def rootCovariance (v:ℝ):Matrix (Fin 2) (Fin 2) ℝ:=fun i j=>if i=0 ∧ j=0 then v else 0

theorem fixed_covariance_leaf_column (ell s h:ℝ)(center:Fin 2→HeatCircle)(i:Fin 2):
    StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center
      (fixedProfile ell s h) 0 i 1=0:=by
  unfold StoppedGaussianFeatures.stoppedCovariance
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun p=>by
    by_cases hp:p.1∈Ioc s h
    · have hn:¬p.1<s:=not_lt_of_ge hp.1.le
      simp only[fixedProfile,hp,ite_true,stoppedRow,targets,show (1:Fin 2)≠0 by decide,ite_false,hn,mul_zero,Pi.zero_apply]
    · simp only[fixedProfile,hp,ite_false,zero_mul,Pi.zero_apply])

theorem fixed_covariance_leaf_row (ell s h:ℝ)(center:Fin 2→HeatCircle)(i:Fin 2):
    StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center
      (fixedProfile ell s h) 0 1 i=0:=by
  unfold StoppedGaussianFeatures.stoppedCovariance
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun p=>by
    by_cases hp:p.1∈Ioc s h
    · have hn:¬p.1<s:=not_lt_of_ge hp.1.le
      simp only[fixedProfile,hp,ite_true,stoppedRow,targets,show (1:Fin 2)≠0 by decide,ite_false,hn,mul_zero,zero_mul,Pi.zero_apply]
    · simp only[fixedProfile,hp,ite_false,zero_mul,Pi.zero_apply])

/-- Only the root sees the old interval, and its covariance is exactly the
literal translated scalar old variance used in the score comparison. -/
theorem fixed_covariance_eq_root {ell s h:ℝ}(hell:0<ell)(hs:0<s)(hsh:s<h)(hh:h≤1)
    (center:Fin 2→HeatCircle):
    StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center
      (fixedProfile ell s h) 0=rootCovariance (oldVariance ell (h-s)):=by
  have hdiag:=native_covariance_diagonal (targets h s) center
    (targets_positive hs hsh) (targets_le_one hsh hh) (fixedProfile ell s h)
    (fixedProfile_measurable ell s h) ell (fixedProfile_bounds hell.le s h) (0:Fin 2)
  simp only[targets,ite_true] at hdiag
  have hvar:=fixedProfile_variance ell s h hs.le hsh (center 0)
  have hscale:=varianceMap_elliptic (c:=fun _=>ell) measurable_const (sub_pos.mpr hsh)
    (show h-s≤1 by linarith) hell.le hell.le (fun _ _ _=>le_rfl) (fun _ _ _=>le_rfl) (0:HeatCircle)
  have hnonneg:0≤varianceMap (fun _=>ell) (h-s) 0:=
    (mul_nonneg (mul_nonneg lowerConstant_pos.le hell.le) (rpow_nonneg (sub_pos.mpr hsh).le _)).trans hscale.1
  have hcoe:(oldVariance ell (h-s):ℝ)=varianceMap (fun _=>ell) (h-s) 0:=Real.coe_toNNReal _ hnonneg
  have h00:=hdiag.trans (hvar.trans hcoe.symm)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rootCovariance] using h00
  · simpa [rootCovariance] using
      fixed_covariance_leaf_column ell s h center 0
  · simpa [rootCovariance] using
      fixed_covariance_leaf_row ell s h center 0
  · simpa [rootCovariance] using
      fixed_covariance_leaf_row ell s h center 1


/-- Literal entry integrability for bounded physical profiles. -/
theorem covariance_entry_integrable {n:ℕ}(target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (ht:∀i,0<target i)(ht1:∀i,target i≤1)(c:Domain→ℝ)(hc:Measurable c)
    (U:ℝ)(hcb:∀p,0≤c p ∧ c p≤U)(i j:Fin n):
    Integrable (fun p=>c p*stoppedRow target target center p i*stoppedRow target target center p j) (historyMeasure 0):=by
  have hi (k:Fin n):MemLp (fun p=>stoppedRow target target center p k) 2 (historyMeasure 0):=by
    apply (memLp_two_iff_integrable_sq (stoppedRow_entry_measurable target target center k).aestronglyMeasurable).mpr
    simpa only[Real.rpow_zero,one_mul] using
      StoppedRowWeighted.weighted_stopped_entry_integrable target target center ht ht1 (fun _=>le_rfl)
        (by norm_num:(-1:ℝ)<0) k
  convert! ((hi i).integrable_mul (hi j)).bdd_mul hc.aestronglyMeasurable
    (ae_of_all _ (fun p=>by rw[Real.norm_eq_abs,abs_of_nonneg (hcb p).1];exact (hcb p).2)) using 1
  funext p
  simp only[Pi.mul_apply]
  ring

def residualProfile (c:Domain→ℝ)(ellOld s h:ℝ)(p:Domain):ℝ:=c p-fixedProfile ellOld s h p

theorem residualProfile_measurable (c:Domain→ℝ)(hc:Measurable c)(ellOld s h:ℝ):
    Measurable (residualProfile c ellOld s h):=hc.sub (fixedProfile_measurable ellOld s h)

theorem residualProfile_bounds {c:Domain→ℝ}{ellOld lower U:ℝ}(hOld:0≤ellOld)
    (hcb:∀p,lower≤c p ∧ c p≤U)(s h:ℝ)(p:Domain):
    lower-ellOld≤residualProfile c ellOld s h p ∧ residualProfile c ellOld s h p≤U:=by
  have hp:=fixedProfile_bounds hOld s h p
  unfold residualProfile
  constructor <;> linarith[(hcb p).1,(hcb p).2]

/-- Exact covariance addition for the true original native rows; no common
stopping window is substituted for the old and newest observations. -/
theorem native_covariance_split {ellOld lower U s h:ℝ}
    (hOld:0<ellOld)(hs:0<s)(hsh:s<h)(hh:h≤1)(hsub:ellOld≤lower)
    (center:Fin 2→HeatCircle)(c:Domain→ℝ)(hc:Measurable c)(hcb:∀p,lower≤c p ∧ c p≤U):
    StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center c 0=
      StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center
        (residualProfile c ellOld s h) 0+rootCovariance (oldVariance ellOld (h-s)):=by
  have hres:∀p,0≤residualProfile c ellOld s h p ∧ residualProfile c ellOld s h p≤U:=by
    intro p
    have hp:=residualProfile_bounds hOld.le hcb s h p
    exact ⟨(sub_nonneg.mpr hsub).trans hp.1,hp.2⟩
  rw[←fixed_covariance_eq_root hOld hs hsh hh center]
  ext i j
  have hir:=covariance_entry_integrable (targets h s) center (targets_positive hs hsh) (targets_le_one hsh hh)
    (residualProfile c ellOld s h) (residualProfile_measurable c hc ellOld s h) U hres i j
  have hik:=covariance_entry_integrable (targets h s) center (targets_positive hs hsh) (targets_le_one hsh hh)
    (fixedProfile ellOld s h) (fixedProfile_measurable ellOld s h) ellOld (fixedProfile_bounds hOld.le s h) i j
  change (∫p,c p*stoppedRow (targets h s) (targets h s) center p i*stoppedRow (targets h s) (targets h s) center p j ∂historyMeasure 0)=
    (∫p,residualProfile c ellOld s h p*stoppedRow (targets h s) (targets h s) center p i*stoppedRow (targets h s) (targets h s) center p j ∂historyMeasure 0)+
      ∫p,fixedProfile ellOld s h p*stoppedRow (targets h s) (targets h s) center p i*stoppedRow (targets h s) (targets h s) center p j ∂historyMeasure 0
  rw[←integral_add hir hik]
  apply integral_congr_ae
  exact ae_of_all _ (fun p=>by dsimp[residualProfile];ring)

/-- The split is genuinely positive at the Gaussian-law level. -/
theorem native_gaussian_positive_split {ellOld lower U s h:ℝ}
    (hOld:0<ellOld)(hs:0<s)(hsh:s<h)(hh:h≤1)(hsub:ellOld≤lower)
    (center:Fin 2→HeatCircle)(c:Domain→ℝ)(hc:Measurable c)(hcb:∀p,lower≤c p ∧ c p≤U):
    multivariateGaussian (0:State 2)
      (StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center c 0)=
    multivariateGaussian (0:State 2)
      (StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center
        (residualProfile c ellOld s h) 0) ∗
      multivariateGaussian 0 (rootCovariance (oldVariance ellOld (h-s))):=by
  have hres:∀p,0≤residualProfile c ellOld s h p ∧ residualProfile c ellOld s h p≤U:=by
    intro p
    have hp:=residualProfile_bounds hOld.le hcb s h p
    exact ⟨(sub_nonneg.mpr hsub).trans hp.1,hp.2⟩
  have hR:(StoppedGaussianFeatures.stoppedCovariance (targets h s) (targets h s) center
      (residualProfile c ellOld s h) 0).PosSemidef:=by
    rw[←weightedFeature_gram (targets h s) (targets h s) center (residualProfile c ellOld s h)
      (residualProfile_measurable c hc ellOld s h) U hres (fun _=>le_rfl) 0]
    exact Matrix.posSemidef_gram ℝ _
  have hK:(rootCovariance (oldVariance ellOld (h-s))).PosSemidef:=by
    rw[←fixed_covariance_eq_root hOld hs hsh hh center,
      ←weightedFeature_gram (targets h s) (targets h s) center (fixedProfile ellOld s h)
        (fixedProfile_measurable ellOld s h) ellOld (fixedProfile_bounds hOld.le s h) (fun _=>le_rfl) 0]
    exact Matrix.posSemidef_gram ℝ _
  rw[gaussian_convolution hR hK,←native_covariance_split hOld hs hsh hh hsub center c hc hcb]

end SHE.NativeOldSplit
