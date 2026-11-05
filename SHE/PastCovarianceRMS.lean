module

public import SHE.PastMeanTimeIntegral
public import SHE.PastMeanDampedTime
public import SHE.HilbertFiniteAverage
public import SHE.RandomProfileEnergy
public import SHE.MarkedProfileTimeFactors
public import SHE.ParentHeatFields
public import SHE.UniformPhysicalScoreForest

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastCovarianceRMS
open Set Filter MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalParentGeometry HistoryProductMeasure
  ControlledOldIntervals QuarterSpatialEvent OrderedHeatForests CoveredHistoryGeometry
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable {R : ReferenceData} (L : Level R HeatCircle 1)

def unitGain (P : CanonicalCovariance.ProfileParameters) (n : ℕ) : ℝ :=
  ControlledProfile.sharpUnit P*((n:ℝ)/(P.lower/2))*
    (1+2/(((P.exponent-1)/4)+1))*2^(-((P.exponent-1)/4))

theorem unitGain_nonneg (P : CanonicalCovariance.ProfileParameters) (n : ℕ) : 0≤unitGain P n := by
  have hU : 0≤ControlledProfile.sharpUnit P:=by
    unfold ControlledProfile.sharpUnit
    exact mul_nonneg (by norm_num) (ProfileStability.meanConstant_nonneg P.lower_pos.le P.holder_nonneg)
  have ha : 0<(P.exponent-1)/4+1:=by linarith [P.exponent_pos]
  unfold unitGain
  exact mul_nonneg (mul_nonneg (mul_nonneg hU
    (div_nonneg (Nat.cast_nonneg n) (half_pos P.lower_pos).le)) (by positivity))
      (rpow_nonneg (by norm_num) _)

theorem gain_identity (P : CanonicalCovariance.ProfileParameters) (n : ℕ)
    {gap : ℝ} (hg : 0<gap) :
    ControlledProfile.sharpUnit P*(((n:ℝ)/(P.lower/2))*(gap/2)^((P.exponent-1)/4)*
      (1+2/(((P.exponent-1)/4)+1)))=
      unitGain P n*gap^(MarkedProfileTimeFactors.freshDegree P-1) := by
  have he : (gap/2)^((P.exponent-1)/4)=
      gap^((P.exponent-1)/4)*2^(-((P.exponent-1)/4)):=by
    rw [Real.div_rpow hg.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_eq_mul_inv]
  rw [he]
  rw [show MarkedProfileTimeFactors.freshDegree P-1=(P.exponent-1)/4 by
    unfold MarkedProfileTimeFactors.freshDegree;ring]
  unfold unitGain
  ring

def coefficient (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (CG : ℝ) : ℝ :=
  sqrt CG*((Fintype.card (Choices 1 k):ℝ)/2)*unitGain P (1+k)

theorem coefficient_nonneg (P : CanonicalCovariance.ProfileParameters) (k : ℕ) (CG : ℝ) :
    0≤coefficient P k CG :=
  mul_nonneg (mul_nonneg (sqrt_nonneg _) (by positivity)) (unitGain_nonneg P _)

/-- Original old-time Minkowski for covariance marks with actual random
score energy. The sharp fresh degree is (beta+3)/4 and the past energy
is retained, without an old-time measure mass loss. -/
theorem old_time_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (q A0 ν CG E : ℝ) (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) (hCG : 0≤CG) (hE : 0≤E)
    (F : (Fin k→ℝ)×Ω→V) (hF : Measurable F)
    (hs : ∀ᵐ t ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)),
      active L T k q t→
      let a:=anchor k t
      let scale:=timeWeight L (fraction P*P.lower) (uniformConstant 1) k a*
        PastWordTimeFields.total L P k a A0 ν/2
      let gain:=ControlledProfile.sharpUnit P*(((1+k:ℕ):ℝ)/(P.lower/2)*
        (((carrier L k).terminal a-q)/2)^((P.exponent-1)/4)*(1+2/(((P.exponent-1)/4)+1)))
      Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧
        (∫ ω,‖F (t,ω)‖^2 ∂μ)≤(CG*scale^2)*(gain^2*E)*(Fintype.card (Choices 1 k):ℝ)^2)
    (hz : ∀ t,¬active L T k q t→∀ ω,F (t,ω)=0) :
    let old:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
    let K:=coefficient P k CG*sqrt E
    Integrable F (old.prod μ) ∧
      Integrable (fun ω=>‖∫ t,F (t,ω) ∂old‖^2) μ ∧
      (∫ ω,‖∫ t,F (t,ω) ∂old‖^2 ∂μ)≤
        (K*QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
          k (T-R.base) (q-R.base) (MarkedProfileTimeFactors.freshDegree P) A0 ν)^2 := by
  intro old K
  have hell : 0<fraction P*P.lower:=mul_pos (fraction_pos P) P.lower_pos
  have hCs : ∀ j,0≤uniformConstant 1 j:=fun j=>(uniformConstant_pos 1 j).le
  let D:=fun t : Fin k→ℝ=>PastMeanTimeFactors.totalIntegrand L P (fraction P*P.lower) (uniformConstant 1)
    k q (MarkedProfileTimeFactors.freshDegree P) A0 ν (anchor k t)
  have hDi:=PastMeanTimeFactors.old_time_budget L P T hT hell (uniformConstant 1) hCs k
    hqbase hqT hTH (MarkedProfileTimeFactors.freshDegree_pos P)
      (MarkedProfileTimeFactors.freshDegree_le_one P) hA0 hν
  have hDm : Measurable D:=(PastMeanTimeFactors.totalIntegrand_measurable L P (fraction P*P.lower)
    (uniformConstant 1) k q (MarkedProfileTimeFactors.freshDegree P) A0 ν).comp (anchor_measurable k)
  have hDn (t) : 0≤D t:=PastMeanTimeFactors.totalIntegrand_nonneg L P hell (uniformConstant 1) hCs k q
    (MarkedProfileTimeFactors.freshDegree P) A0 ν _
  have hK : 0≤K:=mul_nonneg (coefficient_nonneg P k CG) (sqrt_nonneg _)
  have hsec : ∀ᵐ t ∂old,Integrable (fun ω=>‖F (t,ω)‖^2) μ ∧
      (∫ ω,‖F (t,ω)‖^2 ∂μ)≤(K*D t)^2 := by
    filter_upwards [hs] with t ht
    by_cases ha : active L T k q t
    · have hh:=ht ha
      have hg : q<(carrier L k).terminal (anchor k t):=by
        simpa only [anchor,ActualMeanKernel.terminal_separated L T hT] using ha.2
      have he:=gain_identity P (1+k) (sub_pos.mpr hg)
      refine ⟨hh.1,hh.2.trans_eq ?_⟩
      rw [he]
      dsimp only [D,K,coefficient]
      rw [PastMeanTimeFactors.totalIntegrand,if_pos ⟨ha.1,hg⟩]
      simp only [mul_pow,Real.sq_sqrt hCG,Real.sq_sqrt hE]
      ring
    · have hzero:=hz t ha
      simp only [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),integrable_const,integral_zero,true_and]
      exact sq_nonneg _
  have hh:=HilbertParameterAverage.finite_energy μ old F hF (fun t=>K*D t)
    (measurable_const.mul hDm) (hDi.1.const_mul K) (fun t=>mul_nonneg hK (hDn t))
      (hsec.mono (fun _ h=>h.1)) (hsec.mono (fun _ h=>h.2))
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  apply pow_le_pow_left₀ (integral_nonneg (fun t=>mul_nonneg hK (hDn t))) _ 2
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hDi.2 hK

end SHE.PastCovarianceRMS
