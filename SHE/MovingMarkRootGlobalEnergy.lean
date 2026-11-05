module

public import SHE.MovingMarkRootPhysicalEnergy
public import SHE.MovingPastSpatialEnergy

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMarkRootGlobalEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMarkRootGlobalEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMarkRootGlobalEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMarkRootGlobalEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMarkRootGlobalEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMarkRootGlobalEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMarkRootGlobalEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMarkRootGlobalEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMarkRootGlobalEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMarkRootGlobalEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMarkRootGlobalEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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
/-- Actual moving-window covariance energy on past/current/sample space.
Original histories and theta are averaged before squaring; the bound
retains the true global difference energy linearly. -/
theorem covariance_global_L2 (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (hh : 0<h)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0<ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0) :
    let CG:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let K:=PastCovarianceRMS.coefficient P k CG
    let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    let νs:=volume.restrict (Ioc (0:ℝ) (h:ℝ))
    Integrable (fun z=>‖CF k z‖^2) (νv.prod (νs.prod (μ.prod AddCircle.haarAddCircle))) ∧
      (∫ z,‖CF k z‖^2 ∂νv.prod (νs.prod (μ.prod AddCircle.haarAddCircle)))≤K^2*
        MovingProfileBudget.covarianceMass P (fraction P*P.lower) (uniformConstant 1) k h A0 ν*Mglobal := by
  intro CG K Mglobal νv νs
  have hm:=MovingMarkRootTheta.covarianceField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmallPoint k
  apply MovingPastSpatialEnergy.from_spatial_sections 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH Bpast hBDGpast (μ.prod AddCircle.haarAddCircle) h (CF k) hm (K^2) ?_
    (MovingProfileBudget.covariance P (fraction P*P.lower) (uniformConstant 1) k h A0 ν)
    (MovingProfileBudget.covariance_measurable P _ _ _ _ _ _)
    (MovingProfileBudget.covariance_square_integrable P _ _ _ _ _ _ (by exact_mod_cast hh) hν)
  · intro v s hv
    exact MovingMarkRootPhysicalEnergy.covariance_section 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
      hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν.le hjet Bpast hBDGpast B0 hBDG v s hv
  · intro v s hv ω
    exact if_neg hv
  · exact sq_nonneg _

include hIJ₀ hIJ₁ in
/-- Actual moving-window baseline energy on past/current/sample space.
Original histories and theta are averaged before squaring; the bound
retains the true global difference energy linearly. -/
theorem baseline_global_L2 (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ) (hH : (H:ℝ)≤1) (hh : 0<h)
    (hsmallPoint : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(h:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (h:ℝ)≤P.horizon) (k : ℕ) (hold : ∀ j,j<k→(h:ℝ)≤uniformHorizon 1 j)
    (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0<ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0) :
    let C:=MixedPastBaselineRMS.momentConstant P k
      ((NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let N:=(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
    let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    let νv:=volume.restrict (Ioc (0:ℝ) (H:ℝ))
    let νs:=volume.restrict (Ioc (0:ℝ) (h:ℝ))
    Integrable (fun z=>‖BF k z‖^2) (νv.prod (νs.prod (μ.prod AddCircle.haarAddCircle))) ∧
      (∫ z,‖BF k z‖^2 ∂νv.prod (νs.prod (μ.prod AddCircle.haarAddCircle)))≤C*N^2*
        MovingProfileBudget.baselineMass P (fraction P*P.lower) (uniformConstant 1) k h A0 ν*Mglobal := by
  intro C N Mglobal νv νs
  have hm:=MovingMarkRootTheta.baselineField_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P P.coefficient haP h Z htarget hstop F hF hFm hΛ hsmallPoint k
  apply MovingPastSpatialEnergy.from_spatial_sections 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH Bpast hBDGpast (μ.prod AddCircle.haarAddCircle) h (BF k) hm (C*N^2) ?_
    (MovingProfileBudget.baseline P (fraction P*P.lower) (uniformConstant 1) k h A0 ν)
    (MovingProfileBudget.baseline_measurable P _ _ _ _ _ _)
    (MovingProfileBudget.baseline_square_integrable P _ _ _ _ _ _ (by exact_mod_cast hh) hν)
  · intro v s hv
    exact MovingMarkRootPhysicalEnergy.baseline_section 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP h Z htarget hstop F hF hFm J hIJ₀ hIJ₁ hlocal hΛ hH hsmallPoint hsmallL2
      hages hrootStop hrootTarget hcenter hspan k hold A0 ν hA0 hν.le hjet Bpast hBDGpast B0 hBDG v s hv
  · intro v s hv ω
    exact if_neg hv
  · exact mul_nonneg (MixedPastBaselineRMS.momentConstant_nonneg P k _) (sq_nonneg _)

end SHE.MovingMarkRootGlobalEnergy
