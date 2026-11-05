module

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

namespace SHE.MovingMeanRootRealization
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanRootRealization_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanRootRealization_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanRootRealization_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanRootRealization_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanRootRealization_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanRootRealization_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanRootRealization_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanRootRealization_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanRootRealization_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanRootRealization_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

include hIJ₀ hIJ₁ in
/-- The weighted Hilbert field in the global moving-past estimate is
exactly the massive Fourier realization of the literal mean leg in the
root-retained three-piece FTC, after every original history/theta average. -/
theorem actual_mean_realization (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1)
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
    (B0 Babs : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (hBDGabs : StandardTerminalBDGPower (k+2) J Babs)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) :
    let G:=fun ω x=>Complex.ofReal (MixedNativeRootThreeLeg.meanAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s) (ω,x))
    ∀ᵐ ω ∂μ,
      (∀ n,fourierCoeff (Avg k mass ρ hmass hρ.le (v,(s,ω))) n=
        (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (G ω) n) ∧
      Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff (G ω) n‖^2) ∧
      (∑' n : ℤ,(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff (G ω) n‖^2)=
        ‖Avg k mass ρ hmass hρ.le (v,(s,ω))‖^2 := by
  intro G
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
  have hh:=MixedPastMeanThetaFourier.actual_theta_fourier 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
    hlocal hΛ hages' hroot' htarg' hcenter (by simpa only [hbsub] using hspan) k
    (by simpa only [hbsub] using hfresh) (by simpa only [hbsub] using hold)
    A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 Babs hBDG hBDGabs
    mass ρ hmass hρ hρhalf (v+s) (le_self_add) hqb hqH hq1
  have he (ω : Ω) : Avg k mass ρ hmass hρ.le (v,(s,ω))=
      MixedPastMeanThetaFourier.weightedAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k (v+s) mass ρ hmass hρ.le ω := by
    unfold MovingMeanThetaEnergy.thetaValue MixedPastMeanThetaFourier.weightedAverage
    apply integral_congr_ae
    filter_upwards with θ
    exact MovingMeanSectionEnergy.value_eq_average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm hages hrootStop k mass ρ hmass hρ.le v s θ ω
  filter_upwards [hh] with ω hω
  rw [←he ω] at hω
  exact ⟨hω,NativeFourierAverage.energy_of_identified mass ρ hmass _ (G ω) hω⟩

end SHE.MovingMeanRootRealization

