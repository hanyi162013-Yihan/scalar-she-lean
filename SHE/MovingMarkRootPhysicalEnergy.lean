module

public import SHE.MovingCovarianceRootSections
public import SHE.MovingBaselineRootSections

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkRootPhysicalEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkRootPhysicalEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkRootPhysicalEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkRootPhysicalEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkRootPhysicalEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkRootPhysicalEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkRootPhysicalEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMarkRootPhysicalEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkRootPhysicalEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkRootPhysicalEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkRootPhysicalEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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



local notation "CV"=>MovingMarkPhysical.covarianceValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "CT"=>MovingMarkRootTheta.covarianceTheta 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

local notation "CF"=>MovingMarkRootTheta.covarianceField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm
local notation "BF"=>MovingMarkRootTheta.baselineField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P P.coefficient haP h Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
theorem covariance_section (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (v s : ℝ) (hv : MovingMeanPhysicalField.valid H h v s) :
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let K:=PastCovarianceRMS.coefficient P k CG
    let En:=∫ ω,‖S.second v.toNNReal ω-S.first v.toNNReal ω‖^2 ∂μ
    Integrable (fun ω=>‖CF k (v,(s,ω))‖^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫ ω,‖CF k (v,(s,ω))‖^2 ∂μ.prod AddCircle.haarAddCircle)≤K^2*
        (MovingProfileBudget.covariance P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s)^2*En := by
  intro CG K En
  have hvco : (v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1
  have hsco : (s.toNNReal:ℝ)=s:=Real.coe_toNNReal _ hv.2.1.le
  have hvH : v.toNNReal+h≤H:=by exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) by rw [hvco];exact hv.2.2.2)
  have hs : (0:ℝ≥0)<s.toNNReal:=by exact_mod_cast (show (0:ℝ)<(s.toNNReal:ℝ) by rw [hsco];exact hv.2.1)
  have hsh : s.toNNReal<h:=by exact_mod_cast (show (s.toNNReal:ℝ)<(h:ℝ) by rw [hsco];exact hv.2.2.1)
  have hh:=MovingCovarianceRootSections.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet Bpast hBDGpast B0 hBDG
    v.toNNReal s.toNNReal hvH hs hsh
  simpa only [MovingMarkRootTheta.covarianceField,if_pos hv,Real.norm_eq_abs,hsco] using hh

include hIJ₀ hIJ₁ in
theorem baseline_section (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (v s : ℝ) (hv : MovingMeanPhysicalField.valid H h v s) :
    let C:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let N:=(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
    let En:=∫ ω,‖S.second v.toNNReal ω-S.first v.toNNReal ω‖^2 ∂μ
    Integrable (fun ω=>‖BF k (v,(s,ω))‖^2) (μ.prod AddCircle.haarAddCircle) ∧
      (∫ ω,‖BF k (v,(s,ω))‖^2 ∂μ.prod AddCircle.haarAddCircle)≤C*N^2*
        (MovingProfileBudget.baseline P (fraction P*P.lower) (uniformConstant 1) k h A0 ν s)^2*En := by
  intro C N En
  have hvco : (v.toNNReal:ℝ)=v:=Real.coe_toNNReal _ hv.1
  have hsco : (s.toNNReal:ℝ)=s:=Real.coe_toNNReal _ hv.2.1.le
  have hvH : v.toNNReal+h≤H:=by exact_mod_cast (show (v.toNNReal:ℝ)+(h:ℝ)≤(H:ℝ) by rw [hvco];exact hv.2.2.2)
  have hs : (0:ℝ≥0)<s.toNNReal:=by exact_mod_cast (show (0:ℝ)<(s.toNNReal:ℝ) by rw [hsco];exact hv.2.1)
  have hsh : s.toNNReal<h:=by exact_mod_cast (show (s.toNNReal:ℝ)<(h:ℝ) by rw [hsco];exact hv.2.2.1)
  have hh:=MovingBaselineRootSections.actual_section_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
    hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν hjet Bpast hBDGpast B0 hBDG
    v.toNNReal s.toNNReal hvH hs hsh
  simpa only [MovingMarkRootTheta.baselineField,if_pos hv,Real.norm_eq_abs,hsco] using hh

end SHE.MovingMarkRootPhysicalEnergy
