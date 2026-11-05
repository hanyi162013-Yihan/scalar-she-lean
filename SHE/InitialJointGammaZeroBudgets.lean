module
public import SHE.InitialNativeColumnEnergy
public import SHE.MixedNativeJointRowBudgets
public import SHE.MixedNativeFrozenFactorPositive
public import SHE.JointGammaFrozenCanonical
public import SHE.JointGammaRootHilbertPair
public import SHE.FirstGammaTerminalReferenceEnergy
public import SHE.JointGammaRootScalarPair
public import SHE.JointGammaOriginalHilbert
public import SHE.NativeBesselDifferenceIdentity
public import SHE.NativeBesselFiniteIdentity
public import SHE.MixedNativePairedRootZero
public import SHE.JointGammaRootRecursion
public import SHE.ControlledScalarReference
public import SHE.JointGammaActualEndpointPair
public import SHE.JointGammaFirstPairRecursion
public import SHE.JointGammaOriginalRegrouping

public import SHE.JointGammaEndpointCurrentNative
public import SHE.FirstGammaEndpointReferenceNative
public import SHE.NativeJointCurrentEndpoint
public import SHE.JointGammaEndpointValues
public import SHE.JointGammaOriginalIto
public import SHE.JointGammaNativeInput
public import SHE.JointGammaEndpointIto
public import SHE.JointGammaNativeRaw
public import SHE.JointGammaNativeNoise
public import SHE.NativeGammaDamping
public import SHE.JointGammaNativeGradients
public import SHE.JointGammaNativeRows
public import SHE.JointGammaScalarNoise
public import SHE.NativeJointPhysicalGammaAlgebra
public import SHE.JointGammaNativeCurrentTime
public import SHE.JointGammaNativeReferenceTime
public import SHE.NativeCanonicalVarianceIdentity
public import SHE.NativeJointGammaFields
public import SHE.JointGammaCurrentTime
public import SHE.NativeJointCurrentSections
public import SHE.JointGammaCurrentIdentity
public import SHE.NativeJointGammaCurrent
public import SHE.JointInterpolationFields
public import SHE.ScalarCovarianceTailScale
public import SHE.NativeScalarProductAlgebra
public import SHE.JointGammaAffine
public import SHE.FirstGammaEndpointPhysical
public import SHE.FirstGammaEndpointCoherence
public import SHE.FirstGammaCurrentIdentity
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.InitialJointGammaZeroBudgets
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaOriginalIto_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaOriginalIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaOriginalIto_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaOriginalIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaOriginalIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaOriginalIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaOriginalIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P:CanonicalCovariance.ProfileParameters) (hκP:κ<P.lower) (hΛ:0≤Λ) (b:ℝ≥0) (hbH:b≤H) (hH:(H:ℝ)≤1)
variable (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hb0:0<b) (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0) (hBDG0:StandardTerminalBDG16 I₀ B0) (hBDG1:StandardTerminalBDG16 I₁ B1)
variable (hsmallL2:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
variable (hlocal:StandardTerminalPastLocality I₁) (Bnext:ℝ≥0) (hBDGnext:StandardTerminalBDGPower 1 I₁ Bnext)
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local notation "Budget"=>MixedNativeJointRowBudgets.timeBudget 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP 0 b hbH hH
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){A ρ:ℝ}(hA:0≤A)
variable (hρ0:-(1/2:ℝ)<ρ) (hρ1:ρ<1/2) (hholder:∀x y,|a x-a y|≤A*|x-y|^P.exponent) (j:ℕ)

include hIJ₀ hIJ₁ hΛ hb0 hsmallL2 hBDGpast hnull hBDG0 hBDG1 ha hA hρ0 hρ1 hholder in
/-- The actual current-variance and frozen-variance positive masses
vanish at the common initial past, for every positive terminal. -/
theorem variance_zero(hwindow:(b:ℝ)≤P.horizon):Budget a j ρ 1 2=0 ∧ Budget a j ρ 4 5=0:=by
  have hz:=InitialNativeColumnEnergy.initial_energy_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hc:=MixedNativeJointRowBudgets.current_variance
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP)
    (hΛ:=hΛ) (v:=0) (b:=b) (hvb:=hb0) (hbH:=hbH) (hH:=hH) (hwindow:=by simpa only [NNReal.coe_zero,sub_zero] using hwindow)
    (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 j
  have hr:=MixedNativeJointRowBudgets.reference_variance
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP)
    (hΛ:=hΛ) (v:=0) (b:=b) (hvb:=hb0) (hbH:=hbH) (hH:=hH) (hwindow:=by simpa only [NNReal.coe_zero,sub_zero] using hwindow)
    (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 j
  rw [hz,mul_zero,ENNReal.ofReal_zero] at hc hr
  exact ⟨le_antisymm hc bot_le,le_antisymm hr bot_le⟩

include hIJ₀ hIJ₁ hΛ hb0 hsmallL2 hBDGpast hnull hBDG0 hBDG1 hBDG hlocal hBDGnext ha hA hρ0 hρ1 hholder in
/-- The compatible frozen-root row mass vanishes at the true initial
past; its clipped past energy is exactly zero. -/
theorem reference_zero(hwindow:(b:ℝ)≤P.horizon):Budget a j ρ 3 4=0:=by
  have hz:=InitialNativeColumnEnergy.initial_energy_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have he:=MixedNativeJointRowBudgets.reference_root
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP)
    (hΛ:=hΛ) (v:=0) (b:=b) (hvb:=hb0) (hbH:=hbH) (hH:=hH) (hwindow:=by simpa only [NNReal.coe_zero,sub_zero] using hwindow)
    (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (B:=B) (hBDG:=hBDG)
    ha hA hρ0 hρ1 hholder hnull B0 B1 hBDG0 hBDG1 hlocal Bnext hBDGnext j
  simp only [hz,mul_zero,zero_div,min_eq_right zero_le_one,ENNReal.ofReal_zero] at he
  exact le_antisymm he bot_le

include hIJ₀ hIJ₁ hΛ hb0 hsmallL2 hBDGpast hbH hH hρ0 hρ1 in
/-- The full changed frozen-coefficient trace mass vanishes at the
same common initial past. -/
theorem factor_zero(hwindow:(b:ℝ)≤P.horizon):
    (∫⁻τ in Set.Ioc (0:ℝ) (b:ℝ),∫⁻ω,ENNReal.ofReal
      (MixedNativeFrozenFactorPositive.density 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hκP 0 b A ρ j τ ω) ∂μ)=0:=by
  have hz:=InitialNativeColumnEnergy.initial_energy_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have he:=MixedNativeFrozenFactorPositive.energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (haU:=haU) (haV:=haV) (hell:=hell) (hbU:=hbU) (hbV:=hbV)
    (I₀:=I₀) (I₁:=I₁) (u₀:=u₀) (S:=S) (J:=J) (hIJ₀:=hIJ₀) (hIJ₁:=hIJ₁) (P:=P) (hκP:=hκP)
    (hΛ:=hΛ) (v:=0) (b:=b) (hvb:=hb0) (hbH:=hbH) (hH:=hH) (hwindow:=by simpa only [NNReal.coe_zero,sub_zero] using hwindow)
    (hsmall:=hsmallL2) (Bpast:=Bpast) (hBDGpast:=hBDGpast) (A:=A) hρ0 hρ1 j
  simpa only [MixedNativeFrozenFactorPositive.budget,hz,mul_zero,ENNReal.ofReal_zero,NNReal.coe_zero,sub_zero,nonpos_iff_eq_zero] using he
end SHE.InitialJointGammaZeroBudgets
