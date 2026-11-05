module

public import SHE.MovingMeanSectionEnergy
public import SHE.MeanThetaAverage
public import SHE.MovingMeanCost

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanThetaEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanThetaEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanThetaEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanThetaEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanThetaEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanThetaEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanThetaEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanThetaEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanThetaEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanThetaEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanThetaEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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

/-- Interpolation is averaged in the actual Hilbert output, after all
old times and before any squared norm. -/
def thetaValue (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (z : ℝ≥0×(ℝ≥0×Ω)) : CircleL2 :=
  ∫ θ,Val k mass ρ hmass hρ (θ,z) ∂MeanThetaAverage.thetaMeasure
local notation "Avg"=>thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

theorem thetaValue_measurable (hΛ : 0≤Λ) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) :
    Measurable (Avg k mass ρ hmass hρ) :=
  (MovingMeanSectionEnergy.value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hΛ k mass ρ hmass hρ).stronglyMeasurable.integral_prod_left'.measurable

variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- The exact current-energy and Lambda powers survive interpolation
averaging with the original random past kept in the same sample. -/
theorem actual_theta_section_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower ((2*p)*(k+2)) J B0)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ε : ℝ) (hε : 0≤ε) (hεhalf : ε<1/2)
    (v s : ℝ≥0) (hvH : v+h≤H) (hs : 0<s) (hsh : s<h) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let C:=((CD+CG)/2)^(1/(p:ℝ))
    let K:=PastMeanRMS.coefficient P k ρ C
    let En:=∫ ω,‖S.second (v+s) ω-S.first (v+s) ω‖^2 ∂μ
    Integrable (fun ω=>‖Avg k mass ρ hmass hρ.le (v,(s,ω))‖^2) μ ∧
      (∫ ω,‖Avg k mass ρ hmass hρ.le (v,(s,ω))‖^2 ∂μ)≤
        (K*((h:ℝ)-s)^(ρ/2)*En^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
          QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
            k h s (1/2-ε) A0 ν)^2 := by
  intro N CG CD C K En
  let Rms:=K*((h:ℝ)-s)^(ρ/2)*En^(χ/2)*((4:ℝ)^ε*Λ^(-ε))*
    QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1)
      k h s (1/2-ε) A0 ν
  let G : ℝ×Ω→CircleL2:=fun z=>Val k mass ρ hmass hρ.le (z.1,(v,(s,z.2)))
  have hG : Measurable G:=
    (MovingMeanSectionEnergy.value_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm hΛ.le k mass ρ hmass hρ.le).comp
      (measurable_fst.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  have hsθ : ∀ᵐ θ ∂MeanThetaAverage.thetaMeasure,
      Integrable (fun ω=>‖G (θ,ω)‖^2) μ ∧ (∫ ω,‖G (θ,ω)‖^2 ∂μ)≤|Rms|^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have ht : |θ|≤1:=by rw [abs_of_nonneg hθ.1.le];exact hθ.2
    simpa only [G,Rms,sq_abs] using
      MovingMeanSectionEnergy.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH
        hages hrootStop hrootTarget hcenter hspan k hfresh hold θ ht A0 ν hA0 hν hjet
        χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf ε hε hεhalf v s hvH hs hsh
  have he:=HilbertParameterAverage.energy μ MeanThetaAverage.thetaMeasure G hG (fun _=>|Rms|)
    measurable_const (integrable_const _) (fun _=>abs_nonneg _)
    (hsθ.mono (fun _ h=>h.1)) (hsθ.mono (fun _ h=>h.2))
  refine ⟨he.2.1,?_⟩
  simpa only [integral_const,probReal_univ,one_smul,sq_abs,thetaValue,G] using he.2.2

end SHE.MovingMeanThetaEnergy

