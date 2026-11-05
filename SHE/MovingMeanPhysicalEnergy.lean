module

public import SHE.MovingMeanPhysicalField
public import SHE.MixedMovingMeanBudget

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanPhysicalEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanPhysicalEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanPhysicalEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanPhysicalEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanPhysicalEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanPhysicalEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanPhysicalEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanPhysicalEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanPhysicalEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanPhysicalEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanPhysicalEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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




local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
local notation "Fv"=>MovingMeanPhysicalField.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Actual old-time-and-theta averaged mean section, on the physical
moving clock, with exact current-energy power and Lambda damping gain. -/
theorem actual_physical_section_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
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
    (v s : ℝ) (hv : MovingMeanPhysicalField.valid H h v s) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let C:=((CD+CG)/2)^(1/(p:ℝ))
    let K:=PastMeanRMS.coefficient P k ρ C
    let En:=∫ ω,‖S.second (v.toNNReal+s.toNNReal) ω-S.first (v.toNNReal+s.toNNReal) ω‖^2 ∂μ
    Integrable (fun ω=>‖Fv k mass ρ hmass hρ.le (v,(s,ω))‖^2) μ ∧
      (∫ ω,‖Fv k mass ρ hmass hρ.le (v,(s,ω))‖^2 ∂μ)≤
        (K*(4:ℝ)^ε)^2*Λ^(-2*ε)*
          MovingMeanKernelMass.kernel P (fraction P*P.lower) (uniformConstant 1) k ρ h (1/2-ε) A0 ν s*En^χ := by
  intro N CG CD C K En
  have hvco : (v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1
  have hsco : (s.toNNReal:ℝ)=s:=Real.coe_toNNReal _ hv.2.1.le
  have hvH : v.toNNReal+h≤H:=by exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) by rw [hvco];exact hv.2.2.2)
  have hs : (0:ℝ≥0)<s.toNNReal:=by exact_mod_cast (show (0:ℝ)<(s.toNNReal:ℝ) by rw [hsco];exact hv.2.1)
  have hsh : s.toNNReal<h:=by exact_mod_cast (show (s.toNNReal:ℝ)<(h:ℝ) by rw [hsco];exact hv.2.2.1)
  have hh:=MovingMeanThetaEnergy.actual_theta_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH
    hages hrootStop hrootTarget hcenter hspan k hfresh hold A0 ν hA0 hν hjet
    χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf ε hε hεhalf
    v.toNNReal s.toNNReal hvH hs hsh
  have he (ω : Ω) : Fv k mass ρ hmass hρ.le (v,(s,ω))=
      Avg k mass ρ hmass hρ.le (v.toNNReal,(s.toNNReal,ω)) :=
    MovingMeanPhysicalField.field_of_valid 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm k mass ρ hmass hρ.le v s hv ω
  simp_rw [he]
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  simp only [hsco]
  exact MovingMeanCost.identity P (fraction P*P.lower) (uniformConstant 1)
    k ρ h (1/2-ε) A0 ν s K ε Λ En χ hΛ.le (integral_nonneg (fun _=>sq_nonneg _))

end SHE.MovingMeanPhysicalEnergy

