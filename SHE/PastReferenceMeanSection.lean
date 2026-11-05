module

public import SHE.MovingMeanSectionEnergy
public import SHE.MovingMeanCanonical
public import SHE.MixedMovingMeanBudget

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.PastReferenceMeanSection
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanSectionEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanSectionEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanSectionEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanSectionEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanSectionEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanSectionEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanSectionEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanSectionEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanSectionEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanSectionEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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


open MovingMeanSectionEnergy
local notation "Val"=>MovingMeanSectionEnergy.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- The quantitative section estimate is now attached to the genuine
jointly Borel moving-window field. It retains the actual current
difference energy, every old assignment gain, and the damping power. -/
theorem actual_section_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ)
    (hfresh : (h:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (θ : ℝ) (hθ : |θ|≤1) (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (χ : ℝ) (hχ0 : 0≤χ) (hχ1 : χ<1) (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ε : ℝ) (hε : 0≤ε) (hεhalf : ε<1/2)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0≤s) (hsh : s<h) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let C:=((CD+CG)/2)^(1/(p:ℝ))
    let K:=PastMeanRMS.coefficient P k ρ C
    let En:=∫ ω,‖S.second (v+s) ω-S.first (v+s) ω‖^2 ∂μ
    Integrable (fun ω=>‖Val k mass ρ hmass hρ.le (θ,(v,(s,ω)))‖^2) μ ∧
      (∫ ω,‖Val k mass ρ hmass hρ.le (θ,(v,(s,ω)))‖^2 ∂μ)≤
        (K*((h:ℝ)-s)^(ρ/2)*En^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k h s (1/2-ε) A0 ν)^2 := by
  intro N CG CD C K En
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
  have hremain : ((v+h:ℝ≥0):ℝ)-((v+s:ℝ≥0):ℝ)=(h:ℝ)-(s:ℝ):=by simp only [NNReal.coe_add];ring
  have hqb : v+s<v+h:=by exact_mod_cast (show (v:ℝ)+(s:ℝ)<(v:ℝ)+(h:ℝ) by linarith [show (s:ℝ)<(h:ℝ) from hsh])
  have hqH : v+s≤H:=(le_of_lt hqb).trans hvH
  have hq1 : ((v+s:ℝ≥0):ℝ)≤1:=(show ((v+s:ℝ≥0):ℝ)≤(H:ℝ) from by exact_mod_cast hqH).trans hH
  have hh:=MixedPastMeanAverage.actual_averaged_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
    hlocal hΛ hages' hroot' htarg' hcenter
    (by simpa only [hbsub] using hspan) k
    (by simpa only [hbsub] using hfresh) (by simpa only [hbsub] using hold)
    θ hθ A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf
    ε hε hεhalf (v+s) (le_self_add) hqb hqH hq1
  have he : (fun ω=>Val k mass ρ hmass hρ.le (θ,(v,(s,ω))))=
      fun ω=>MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k
        (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))))
        θ (v+s) mass ρ hmass hρ.le ω:=funext (fun ω=>
    value_eq_average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      hages hrootStop k mass ρ hmass hρ.le v s θ ω)
  have heval (ω : Ω):=congrFun he ω
  simp_rw [heval]
  constructor
  · simpa only [MixedPastMeanFields.average] using hh.2.1
  · simpa only [MixedPastMeanFields.average,hbsub,hqsub,hremain] using hh.2.2

end SHE.PastReferenceMeanSection
