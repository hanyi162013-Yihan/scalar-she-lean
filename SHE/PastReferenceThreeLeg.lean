module

public import SHE.MovingMarkRootAttachment
public import SHE.MixedNativeRootThreeLeg
public import SHE.MovingMarkRootShift
public import SHE.MovingProfileBudget
public import SHE.MixedPastCovarianceAverageUniform
public import SHE.MixedNativeCovarianceFTCIdentity

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.PastReferenceThreeLeg
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingRootThreeLeg_realSigma : MeasurableSpace RealL2 := borel _
local instance movingRootThreeLeg_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingRootThreeLeg_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingRootThreeLeg_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingRootThreeLeg_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingRootThreeLeg_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingRootThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingRootThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingRootThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingRootThreeLeg_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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



local notation "CV"=>MovingMarkRootFields.covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Exact moving-window reference comparison with the covariance and
baseline legs identified with the actual globally bounded spatial
fields. The entire original-stop mean leg is retained literally. -/
theorem actual_moving_transfer (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0≤s) (hsh : s<h) :
    ∀ᵐ z : Ω×HeatCircle ∂μ.prod AddCircle.haarAddCircle,
      MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 1 (v+s) z-
      MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k 0 (v+s) z=
      CT k (v,(s,z))+
      MixedNativeRootThreeLeg.meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s) z+
      MovingMarkRootTheta.baselineTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P P.coefficient haP h Z htarget hstop F hF hFm k (v,(s,z)) := by
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
  have hqsub : ((v+s:ℝ≥0):ℝ)-(v:ℝ)=(s:ℝ):=by simp only [NNReal.coe_add,add_sub_cancel_left]
  have hqb : v+s<v+h:=by exact_mod_cast (show (v:ℝ)+(s:ℝ)<(v:ℝ)+(h:ℝ) by linarith [show (s:ℝ)<(h:ℝ) from hsh])
  have hqH : v+s≤H:=(le_of_lt hqb).trans hvH
  have hvH' : v≤H:=(show v≤v+h from le_self_add).trans hvH
  have hv1 : (v:ℝ)≤1:=(show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvH').trans hH
  have hq1 : ((v+s:ℝ≥0):ℝ)≤1:=(show ((v+s:ℝ≥0):ℝ)≤(H:ℝ) from by exact_mod_cast hqH).trans hH
  have he:=MixedNativeRootThreeLeg.actual_three_leg_transfer
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
    hlocal hΛ hsmallPoint hsmallL2 hvH' hv1 Bpast hBDGpast
    hages' hroot' htarg' hcenter (by simpa only [hbsub] using hspan) k
    (by simpa only [hbsub] using hfresh) (by simpa only [hbsub] using hold)
    A0 ν hA0 hν hjet B0 hBDG (v+s) le_self_add hqb hqH hq1
  filter_upwards [he] with z hz
  rw [←MovingMarkRootAttachment.covariance_eq_actual_average
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v s z.1 z.2,
    ←MovingMarkRootAttachment.baseline_eq_actual_average
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm k v s z.1 z.2] at hz
  exact hz

end SHE.PastReferenceThreeLeg
