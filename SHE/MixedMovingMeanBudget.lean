module

public import SHE.MixedMovingEnergy
public import SHE.MovingMeanKernelMass
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedMovingMeanBudget
open Set MeasureTheory Real PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedMovingMeanBudget_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedMovingMeanBudget_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedMovingMeanBudget_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedMovingMeanBudget_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedMovingMeanBudget_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedMovingMeanBudget_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedMovingMeanBudget_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedMovingMeanBudget_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedMovingMeanBudget_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedMovingMeanBudget_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedMovingMeanBudget_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedMovingMeanBudget_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
local notation "Ee"=>MixedMovingEnergy.ennEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Mglobal"=>MixedMovingEnergy.globalEnergy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

include hIJ₀ hIJ₁ in
/-- The actual moving-past mean budget retains its exact damping gain,
sharp finite assignment mass, and global SMALL difference-energy
power. Both past-profile and shifted-current slots are covered without
a uniform current-moment substitution. -/
theorem actual_bounds (hΛ : 0≤Λ) (hH : (H:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDGPower 1 J B)
    (P : CanonicalCovariance.ProfileParameters) (scoreEll : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (ρ h fresh A0 ν C ε χ : ℝ)
    (hd : 0<ρ+2*fresh-1) (hh : 0<h) (hν : 0≤ν) (hχ : 0≤χ) (hχ1 : χ≤1) :
    let K:=fun s=>ENNReal.ofReal (C^2*Λ^(-2*ε)*MovingMeanKernelMass.kernel P scoreEll Cs k ρ h fresh A0 ν s)
    let Cost:=ENNReal.ofReal (C^2*Λ^(-2*ε)*
      PastMeanTimeFactors.assignmentMass P scoreEll Cs k ρ h fresh A0 ν*Mglobal^χ*(H:ℝ)^(1-χ))
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) h,K s*(Ee v)^χ)≤Cost ∧
    (∫⁻ v in Ioc (0:ℝ) (H:ℝ),∫⁻ s in Ioc (0:ℝ) h,
      K s*MovingPastFractional.powerWindow (H:ℝ) χ Ee (v+s))≤Cost := by
  intro K Cost
  let g:=C^2*Λ^(-2*ε)
  let A:=PastMeanTimeFactors.assignmentMass P scoreEll Cs k ρ h fresh A0 ν
  have hg : 0≤g:=mul_nonneg (sq_nonneg _) (rpow_nonneg hΛ _)
  have hi:=MovingMeanKernelMass.kernel_mass P scoreEll Cs k ρ h fresh A0 ν hd hh hν
  have hA : 0≤A:=(integral_nonneg (MovingMeanKernelMass.kernel_nonneg P scoreEll Cs k ρ h fresh A0 ν)).trans hi.2
  have hM:=MixedMovingEnergy.globalEnergy_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hK : Measurable K:=ENNReal.measurable_ofReal.comp
    ((MovingMeanKernelMass.kernel_measurable P scoreEll Cs k ρ h fresh A0 ν).const_mul g)
  have hmass : (∫⁻ s in Ioc (0:ℝ) h,K s)≤ENNReal.ofReal (g*A):=by
    rw [←ofReal_integral_eq_lintegral_ofReal (hi.1.const_mul g)
      (ae_of_all _ (fun s=>mul_nonneg hg (MovingMeanKernelMass.kernel_nonneg P scoreEll Cs k ρ h fresh A0 ν s))),
      integral_const_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hi.2 hg)
  have hcost : ENNReal.ofReal (g*A)*(ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))=Cost := by
    have hpM : ENNReal.ofReal Mglobal^χ=ENNReal.ofReal (Mglobal^χ):=
      ENNReal.ofReal_rpow_of_nonneg hM hχ
    have hpH : (ENNReal.ofReal (H:ℝ))^(1-χ)=ENNReal.ofReal ((H:ℝ)^(1-χ)):=
      ENNReal.ofReal_rpow_of_nonneg (show 0≤(H:ℝ) from H.2) (sub_nonneg.mpr hχ1)
    rw [hpM,hpH,
      ←ENNReal.ofReal_mul (rpow_nonneg hM χ),
      ←ENNReal.ofReal_mul (mul_nonneg hg hA)]
    congr 1
    dsimp only [Cost,g,A]
    ring
  have hp:=MixedMovingEnergy.past_window_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH B hBDG K hK h hχ hχ1
  have hc:=MixedMovingEnergy.current_window_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ hH B hBDG K hK h hχ hχ1
  constructor
  · exact hp.trans ((by gcongr : (∫⁻ s in Ioc (0:ℝ) h,K s)*
      (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))≤
        ENNReal.ofReal (g*A)*(ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))).trans_eq hcost)
  · exact hc.trans ((by gcongr : (∫⁻ s in Ioc (0:ℝ) h,K s)*
      (ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))≤
        ENNReal.ofReal (g*A)*(ENNReal.ofReal Mglobal^χ*(ENNReal.ofReal (H:ℝ))^(1-χ))).trans_eq hcost)

end SHE.MixedMovingMeanBudget

