module

public import SHE.MovingMeanPhysicalEnergy

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanGlobalEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanGlobalEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanGlobalEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanGlobalEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanGlobalEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanGlobalEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanGlobalEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanGlobalEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanGlobalEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanGlobalEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanGlobalEnergy_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
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
/-- Full moving-past/current/sample mean energy, after original old
times and theta have been averaged before squaring. The smallness is
the actual GLOBAL difference energy to power chi, with retained
Lambda^(-2 epsilon) and the exact finite assignment budget. -/
theorem actual_global_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0<Λ)
    (hH : (H:ℝ)≤1) (hh : 0<h)
    (Bfirst : ℝ≥0) (hBDGfirst : StandardTerminalBDGPower 1 J Bfirst)
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
    (ε : ℝ) (hε : 0≤ε) (hερ : 2*ε<ρ) :
    let N:=(2*p)*(k+2)
    let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
      ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
    let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
    let C:=((CD+CG)/2)^(1/(p:ℝ))
    let K:=PastMeanRMS.coefficient P k ρ C
    let Mglobal:=MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) (h:ℝ),∫⁻ ω,
      ENNReal.ofReal (‖Fv k mass ρ hmass hρ.le (v,(s,ω))‖^2) ∂μ)≤
      ENNReal.ofReal ((K*(4:ℝ)^ε)^2*Λ^(-2*ε)*
        PastMeanTimeFactors.assignmentMass P (fraction P*P.lower) (uniformConstant 1)
          k ρ h (1/2-ε) A0 ν*Mglobal^χ*(H:ℝ)^(1-χ)) := by
  intro N CG CD C K Mglobal
  let Ee:=MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  let Kg : ℝ→ℝ≥0∞:=fun s=>ENNReal.ofReal ((K*(4:ℝ)^ε)^2*Λ^(-2*ε)*
    MovingMeanKernelMass.kernel P (fraction P*P.lower) (uniformConstant 1) k ρ h (1/2-ε) A0 ν s)
  have hglobal:=MixedMovingMeanBudget.actual_bounds 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ.le hH Bfirst hBDGfirst P (fraction P*P.lower) (uniformConstant 1)
    k ρ h (1/2-ε) A0 ν (K*(4:ℝ)^ε) ε χ (by linarith) (by exact_mod_cast hh) hν hχ0 hχ1.le
  refine (show (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) (h:ℝ),∫⁻ ω,
      ENNReal.ofReal (‖Fv k mass ρ hmass hρ.le (v,(s,ω))‖^2) ∂μ)≤
      ∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) (h:ℝ),
        Kg s*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+s) from ?_).trans hglobal.2
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hvI
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsI
  by_cases hv : MovingMeanPhysicalField.valid H h v s
  · have hsE:=MovingMeanPhysicalEnergy.actual_physical_section_energy
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      J hIJ₀ hIJ₁ hlocal hΛ hH hages hrootStop hrootTarget hcenter hspan k hfresh hold
      A0 ν hA0 hν hjet χ hχ0 hχ1 p hp horder B0 hBDG mass ρ hmass hρ hρhalf
      ε hε (by linarith) v s hv
    let En:=∫ ω,‖S.second (v.toNNReal+s.toNNReal) ω-S.first (v.toNNReal+s.toNNReal) ω‖^2 ∂μ
    have hEn : 0≤En:=integral_nonneg (fun _=>sq_nonneg _)
    have hqWin : v+s∈Ioc (0:ℝ) (H:ℝ):=⟨by linarith [hv.1,hv.2.1],by linarith [hv.2.2.1,hv.2.2.2]⟩
    have hqNN : (v+s).toNNReal=v.toNNReal+s.toNNReal := by
      apply Subtype.ext
      change ((v+s).toNNReal:ℝ)=(v.toNNReal:ℝ)+(s.toNNReal:ℝ)
      rw [Real.coe_toNNReal _ hv.1,Real.coe_toNNReal _ hv.2.1.le,Real.coe_toNNReal _ hqWin.1.le]
    have he : Ee (v+s)=ENNReal.ofReal En := by
      simp only [Ee,MixedMovingEnergy.ennEnergy,MixedMovingEnergy.realEnergy,
        indicator_of_mem hqWin,hqNN,MixedMovingEnergy.energy,En]
    rw [←ofReal_integral_eq_lintegral_ofReal hsE.1 (ae_of_all _ (fun _=>sq_nonneg _))]
    calc
      _≤ENNReal.ofReal ((K*(4:ℝ)^ε)^2*Λ^(-2*ε)*
        MovingMeanKernelMass.kernel P (fraction P*P.lower) (uniformConstant 1) k ρ h (1/2-ε) A0 ν s*En^χ):=
          ENNReal.ofReal_le_ofReal hsE.2
      _=Kg s*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+s) := by
        rw [MovingPastFractional.powerWindow,indicator_of_mem hqWin,he,
          ENNReal.ofReal_rpow_of_nonneg hEn hχ0]
        exact ENNReal.ofReal_mul (mul_nonneg
          (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hΛ.le _))
          (MovingMeanKernelMass.kernel_nonneg P _ _ _ _ _ _ _ _ _))
  · have hz (ω : Ω):=MovingMeanPhysicalField.field_zero
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm
      k mass ρ hmass hρ.le v s hv ω
    simp_rw [hz]
    simp only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),ENNReal.ofReal_zero,lintegral_zero]
    exact bot_le

end SHE.MovingMeanGlobalEnergy

