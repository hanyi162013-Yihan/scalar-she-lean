module

public import SHE.PastReferenceThreeLeg
public import SHE.PastReferenceMeanRealization
public import SHE.PastReferenceCovarianceSection
public import SHE.PastReferenceBaselineSection
public import SHE.NegativeThreeLeg
public import SHE.MixedPastMeanRootL1
public import SHE.MovingRootThreeLeg
public import SHE.MovingMeanRootRealization
public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections
public import SHE.MixedPastMeanThetaFourier
public import SHE.MovingMeanThetaEnergy
public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.PastReferenceComparisonSection
open AddCircle
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingComparisonSection_realSigma : MeasurableSpace RealL2 := borel _
local instance movingComparisonSection_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingComparisonSection_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingComparisonSection_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingComparisonSection_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingComparisonSection_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingComparisonSection_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingComparisonSection_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingComparisonSection_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingComparisonSection_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v



local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BT"=>MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

def endpointDifference (k : ℕ) (v s : ℝ≥0) (z : Ω×HeatCircle) : ℝ:=
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 1 (v+s) z-
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 0 (v+s) z

local notation "End"=>endpointDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- Literal finite reference-tree endpoint comparison in massive spatial
energy. No scalar mean L² premise, Gaussian applicability, or Fubini
premise remains; original histories and theta are averaged first. -/
theorem actual_comparison (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (Bpast Babs B0 : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0≤s) (hsh : s<h) :
    ∀ᵐ ω ∂μ,
      Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*
        ‖fourierCoeff (fun x=>Complex.ofReal (End k v s (ω,x))) n‖^2) ∧
      NativeFourierAverage.scalarEnergy mass ρ (fun x=>Complex.ofReal (End k v s (ω,x)))≤
        3*(mass^(-ρ)*((∫ x,|CT k (v,(s,(ω,x)))|^2 ∂haarAddCircle)+
          (∫ x,|BT k (v,(s,(ω,x)))|^2 ∂haarAddCircle))+
            ‖Avg k mass ρ hmass hρ.le (v,(s,ω))‖^2) := by
  have hsplit:=PastReferenceThreeLeg.actual_moving_transfer 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    Bpast hBDGpast Babs hBDGabs v s hvH hs hsh
  have hmean:=PastReferenceMeanRealization.actual_mean_realization 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder
    B0 Babs hBDG hBDGabs mass ρ hmass hρ hρhalf v s hvH hs hsh
  have hCi:=(PastReferenceCovarianceSection.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet
    Bpast hBDGpast Babs hBDGabs v s hvH hs hsh).1
  have hBi:=(PastReferenceBaselineSection.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ.le hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet
    Bpast hBDGpast Babs hBDGabs v s hvH hs hsh).1
  have hages' : ∀ x i,((ZT v).observations x i).stop≤((ZT v).observations x i).target := by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤(Z.observations x i).target+(v:ℝ)
    linarith [hages x i]
  have hroot' : ∀ x i,((ZT v).observations x i).stop≤((v+h:ℝ≥0):ℝ) := by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤((v+h:ℝ≥0):ℝ)
    rw [NNReal.coe_add]
    linarith [hrootStop x i]
  have htarg' : ∀ x i,((ZT v).observations x i).target=((v+h:ℝ≥0):ℝ) := by
    intro x i
    change (Z.observations x i).target+(v:ℝ)=((v+h:ℝ≥0):ℝ)
    rw [hrootTarget,NNReal.coe_add,add_comm]
  have hbsub : ((v+h:ℝ≥0):ℝ)-(v:ℝ)=(h:ℝ):=by simp only [NNReal.coe_add,add_sub_cancel_left]
  have hqb : v+s<v+h:=by exact_mod_cast (show (v:ℝ)+(s:ℝ)<(v:ℝ)+(h:ℝ) by linarith [show (s:ℝ)<(h:ℝ) from hsh])
  have hqH : v+s≤H:=(le_of_lt hqb).trans hvH
  have hq1 : ((v+s:ℝ≥0):ℝ)≤1:=(show ((v+s:ℝ≥0):ℝ)≤(H:ℝ) from by exact_mod_cast hqH).trans hH
  let Mean:=MixedNativeRootThreeLeg.meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s)
  have hMi : Integrable Mean (μ.prod haarAddCircle):=
    MixedPastMeanRootL1.actual_meanAverage_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
      hlocal hΛ.le hages' hroot' htarg' (by simpa only [hbsub] using hspan) k
      (by simpa only [hbsub] using hfresh) (by simpa only [hbsub] using hold)
      A0 ν hA0 hν hjet Babs hBDGabs (v+s) (le_self_add) hqb hqH hq1
  have hCm : Measurable (fun z : Ω×HeatCircle=>CT k (v,(s,z))):=
    (MovingMarkRootTheta.covarianceTheta_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm hΛ.le hsmallPoint k).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hBm : Measurable (fun z : Ω×HeatCircle=>BT k (v,(s,z))):=
    (MovingMarkRootTheta.baselineTheta_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm hΛ.le hsmallPoint k).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  filter_upwards [Measure.ae_ae_of_ae_prod hsplit,hmean,hCi.prod_right_ae,hBi.prod_right_ae,hMi.prod_right_ae]
    with ω hωsplit hωmean hωC hωB hωM
  have hc : MemLp (fun x=>Complex.ofReal (CT k (v,(s,(ω,x))))) 2 haarAddCircle := by
    apply (memLp_two_iff_integrable_sq_norm
      ((Complex.continuous_ofReal.measurable.comp hCm).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr
    simpa only [Function.comp_apply,id_eq,Complex.norm_real,Real.norm_eq_abs] using hωC
  have hb : MemLp (fun x=>Complex.ofReal (BT k (v,(s,(ω,x))))) 2 haarAddCircle := by
    apply (memLp_two_iff_integrable_sq_norm
      ((Complex.continuous_ofReal.measurable.comp hBm).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr
    simpa only [Function.comp_apply,id_eq,Complex.norm_real,Real.norm_eq_abs] using hωB
  have hspl : (fun x=>Complex.ofReal (End k v s (ω,x)))=ᵐ[haarAddCircle]
      fun x=>Complex.ofReal (CT k (v,(s,(ω,x))))+Complex.ofReal (Mean (ω,x))+
        Complex.ofReal (BT k (v,(s,(ω,x)))) := by
    filter_upwards [hωsplit] with x hx
    exact (congrArg Complex.ofReal hx).trans (by simp only [Complex.ofReal_add,Mean])
  simpa only [Complex.norm_real,Real.norm_eq_abs] using
    NativeFourierAverage.scalar_three_leg_energy mass ρ hmass hρ.le _ _ _ _ hc hb
      (Complex.ofRealCLM.integrable_comp hωM) (Avg k mass ρ hmass hρ.le (v,(s,ω))) hspl hωmean.1

end SHE.PastReferenceComparisonSection
