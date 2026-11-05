module

public import SHE.NativeCanonicalGammaEnergy
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

namespace SHE.MixedNativeGammaEnergy
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

def commonLower : ℝ:=min ell (P.lower-κ)
def commonUpper : ℝ:=max M (P.upper-κ)

include hell hκP in
theorem commonLower_pos : 0<commonLower (ell:=ell) (P:=P) (κ:=κ):=lt_min hell (sub_pos.mpr hκP)

def castCurrent (f : EllipticField ell M) : EllipticField (commonLower (ell:=ell) (P:=P) (κ:=κ)) (commonUpper (M:=M) (P:=P) (κ:=κ)):=
  ⟨f.1,f.2.1,f.2.2.mono (fun _ h=>⟨(min_le_left _ _).trans h.1,h.2.trans (le_max_left _ _)⟩)⟩
theorem castCurrent_measurable : Measurable (castCurrent (ell:=ell) (M:=M) (P:=P) (κ:=κ)):=
  measurable_subtype_coe.subtype_mk

def currentFirst (p : ℝ≥0×Ω) :=castCurrent (P:=P) (κ:=κ) (ContinuousHeatMild.coefficientFunction haU hell hbU S.first p)
def currentSecond (p : ℝ≥0×Ω) :=castCurrent (P:=P) (κ:=κ) (ContinuousHeatMild.coefficientFunction haV hell hbV S.second p)
theorem currentFirst_predictable : Measurable[𝓕.predictable]
    (currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P):=
  (castCurrent_measurable (P:=P) (κ:=κ)).comp S.first_coefficient.measurable
theorem currentSecond_predictable : Measurable[𝓕.predictable]
    (currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P):=
  (castCurrent_measurable (P:=P) (κ:=κ)).comp S.second_coefficient.measurable

include S P hκP hbH hb1 hb0 hnull B0 B1 hBDG0 hBDG1 J ha hA hβ hβ1 hh j hΛ hρ hρhalf in
/-- The COMPLETE original-J stochastic paired-Gamma inequality for the
actual constructed mixed native SPDE pair. Both actual nonlinear
coefficient fields and both actual frozen own-profile fields are used;
all field/predictability/ellipticity/isometry applicability is proved.
The inferred conclusion is exactly NativeCanonicalGammaEnergy's
six-slot integral bound specialized to this S, with no added premise. -/
def actual_complete_energy :=
  NativeCanonicalGammaEnergy.complete_energy
    (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=v) (b:=b) (hbH:=hbH) (hb1:=hb1)
    (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (hU:=S.first_predictable) (hV:=S.second_predictable)
    (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁)
    (hb0:=hb0) (hnull:=hnull) (B0:=B0) (B1:=B1) (hBDG0:=hBDG0) (hBDG1:=hBDG1)
    (ha:=ha) (hA:=hA) (hβ:=hβ) (hβ1:=hβ1) (hh:=hh) (j:=j)
    (L:=Λ) (hL:=hΛ) (ρ:=ρ) (hρ:=hρ) (hρhalf:=hρhalf)
    (m:=commonLower (ell:=ell) (P:=P) (κ:=κ)) (W:=commonUpper (M:=M) (P:=P) (κ:=κ))
    (hm:=commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)) (hmP:=min_le_right _ _) (hWP:=le_max_right _ _)
    (c0:=currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P)
    (c1:=currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P)
    (hc0:=currentFirst_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P)
    (hc1:=currentSecond_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P) J

end SHE.MixedNativeGammaEnergy
