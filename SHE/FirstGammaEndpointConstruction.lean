module

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

namespace SHE.FirstGammaEndpointConstruction
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointConstruction_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointConstruction_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointConstruction_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointConstruction_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointConstruction_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointConstruction_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointConstruction_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointConstruction_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


variable (θ : ℝ)
local notation "R" => FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH
local notation "Rref" => FirstGammaEndpointRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
local notation "K" => FirstGammaEndpointRows.cap (M:=M) Λ κ b
local notation "Kref" => FirstGammaEndpointRows.replacementCap (n:=n) P
local notation "z0" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)

def rows : Fin ((n+n)+(n+n))→Process (E:=Both RealHaarInput) 𝓕 μ H:=
  SingularReferenceSplice.rows 𝓕 μ H b v R Rref
def value : ℝ≥0×Ω→FirstGammaAffine.Space n:=
  SingularReferenceSplice.value 𝓕 μ H b v R Rref J z0

theorem continuous_value (hb0 : 0<b) (ω : Ω) :
    Continuous (fun t=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ (t,ω)):=
  SingularReferenceSplice.continuous_value 𝓕 μ H b v R Rref J z0 hb0 ω

theorem predictable_value (hb0 : 0<b) (hb1 : (b:ℝ)≤1)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B) :
    StronglyMeasurable[𝓕.predictable]
      (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ):=
  SingularReferenceSplice.predictable_value 𝓕 μ H b v R Rref K Kref
    (FirstGammaEndpointRows.cap_nonneg Λ κ hκ hell hbU b)
    (FirstGammaEndpointRows.replacementCap_nonneg P)
    (FirstGammaEndpointRows.actual_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH hb1)
    (FirstGammaEndpointRows.replacement_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ hb1)
    J z0 hbH hb0 hnull B hBDG

theorem integral_representation (hb0 : 0<b) (hb1 : (b:ℝ)≤1)
    (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B) (t : ℝ≥0) :
    (fun ω=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (FiniteReferenceSplice.jointInitial z0)
        (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ) t:=
  SingularReferenceSplice.integral_representation 𝓕 μ H b v R Rref K Kref
    (FirstGammaEndpointRows.cap_nonneg Λ κ hκ hell hbU b)
    (FirstGammaEndpointRows.replacementCap_nonneg P)
    (FirstGammaEndpointRows.actual_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH hb1)
    (FirstGammaEndpointRows.replacement_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ hb1)
    J z0 hbH hb0 B hBDG t

end SHE.FirstGammaEndpointConstruction
