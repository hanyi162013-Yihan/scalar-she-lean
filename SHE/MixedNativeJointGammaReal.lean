module

public import SHE.NativeJointGammaReal
public import SHE.MixedNativeGammaEnergy
public import SHE.FirstGammaCanonicalReference
public import SHE.FirstGammaEndpointPhysical
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
public import SHE.FiniteReferenceSpliceRows
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointGammaReal
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance mixedNativeGammaEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeGammaEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeGammaEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeGammaEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeGammaEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeGammaEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeGammaEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeGammaEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedNativeGammaEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeGammaEnergy_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance mixedNativeGammaEnergy_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1) (hb0 : 0<b)
variable (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I₀ B0) (hBDG1 : StandardTerminalBDG16 I₁ B1)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable {a : ℝ→ℝ} (ha : SmoothCylinders.BoundedSmooth a) {A β : ℝ}
variable (hA : 0≤A) (hβ : 0≤β) (hβ1 : β≤1) (hh : ∀x y,|a x-a y|≤A*|x-y|^β) (j : ℕ)
variable (hΛ : 1≤Λ) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2)

open MixedNativeGammaEnergy
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ S P hκP hbH hb1 hb0 hnull B0 B1 hBDG0 hBDG1 J ha hA hβ hβ1 hh j hΛ hρ hρhalf in
/-- Exact original I0/I1 physical JOINT complete-Gamma energy equals the
SAME original J Fourier energy for the ACTUAL mixed SPDE solution.
All coefficient, profile, real-subspace and predictable input
applicability is proved; this is not a new stochastic input. -/
def actual_physical_energy_eq :=
  NativeJointGammaReal.physical_energy_eq
    (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (hU:=S.first_predictable) (hV:=S.second_predictable)
    (P:=P) (Λ:=Λ) (hΛdamp:=zero_le_one.trans hΛ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁)
    (hb0:=hb0) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hA:=hA) (hβ:=hβ) (hβ1:=hβ1) (hh:=hh) (j:=j)
    (L:=Λ) (hL:=hΛ) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
    (m:=commonLower (ell:=ell) (P:=P) (κ:=κ)) (W:=commonUpper (M:=M) (P:=P) (κ:=κ))
    (hm:=commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)) (hmP:=min_le_right _ _) (hWP:=le_max_right _ _)
    (c0:=currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P)
    (c1:=currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P)
    (hc0:=currentFirst_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P)
    (hc1:=currentSecond_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P) J hIJ₀ hIJ₁

end SHE.MixedNativeJointGammaReal
