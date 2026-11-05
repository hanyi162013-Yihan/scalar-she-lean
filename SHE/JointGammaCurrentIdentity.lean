module

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

namespace SHE.JointGammaCurrentIdentity
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaCurrentIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaCurrentIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaCurrentIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaCurrentIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaCurrentIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaCurrentIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaCurrentIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaCurrentIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local notation "Y" => FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hH B hBDG hIJ₀ hIJ₁ in
/-- The actual singular-endpoint extended martingale gives the literal
joint current, with original target damping and without an old compensator. -/
theorem current_eq_joint (θ : ℝ) (q : ℝ≥0) (hqb : q<b) :
    ∀ᵐ ω∂μ,∀ i,
      JointGammaAffine.current n Λ θ (fun i=>(Z i).target) (Y θ (q,ω)) i=
        functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
          θ*Real.exp (-Λ*((Z i).target-(q:ℝ)))*
            functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω) := by
  have hb0 : 0<b:=(show (0:ℝ≥0)≤q from bot_le).trans_lt hqb
  have hqH : q≤H:=hqb.le.trans hbH
  have hqgap : ∀i,(q:ℝ)<(Z i).target:=fun i=>
    (show (q:ℝ)<(b:ℝ) by exact_mod_cast hqb).trans_le (htarget i)
  have hp:=FirstGammaEndpointPhysical.value_eq_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ q hqgap hH B hBDG hb0 hqb.le q le_rfl
  have hu:=FirstGammaValues.currentU_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v q hqgap hH (hb0.trans_le hbH) B hBDG hIJ₀ hIJ₁ θ hqH q le_rfl
  have hd:=FirstGammaValues.currentD_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z J P hκP hΛ v q hqgap hH (hb0.trans_le hbH) B hBDG hIJ₀ hIJ₁ θ hqH q le_rfl
  filter_upwards [hp,hu,hd] with ω hp hu hd i
  rw [hp,JointGammaAffine.current_apply,hu i,hd i]
  have he : Real.exp (-Λ*(Z i).target)*Real.exp (Λ*(q:ℝ))=
      Real.exp (-Λ*((Z i).target-(q:ℝ))) := by
    rw [←Real.exp_add]
    congr 1
    ring
  linear_combination θ*functional ((Z i).target-(q:ℝ)) (Z i).center
    (S.second q ω-S.first q ω)*he

end SHE.JointGammaCurrentIdentity
