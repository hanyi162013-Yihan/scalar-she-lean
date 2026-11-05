module

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

namespace SHE.FirstGammaEndpointPhysical
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointPhysical_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointPhysical_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointPhysical_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointPhysical_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointPhysical_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointPhysical_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointPhysical_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointPhysical_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open Set StoppedItoInputs
variable (θ : ℝ) (c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)
local notation "Prefix" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "PrefRef" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap θ
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "PrefRows" => FiniteReferenceSplice.jointRows 𝓕 μ H v Prefix PrefRef
local notation "z0" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "YE" => FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ
local notation "YC" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap θ
variable (hH : (H:ℝ)≤1) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)

include hH B hBDG in
/-- The singular endpoint vector is the SAME original-J vector on
every positive-gap prefix, not a replacement solution or restarted law. -/
theorem value_eq_prefix (hb0 : 0<b) (hcb : c≤b) (q : ℝ≥0) (hqc : q≤c) :
    (fun ω=>YE (q,ω))=ᵐ[μ] (fun ω=>YC (q,ω)) := by
  have hH0 : 0<H:=hb0.trans_le hbH
  have hbH' : (b:ℝ)≤(H:ℝ):=by exact_mod_cast hbH
  have hb1 : (b:ℝ)≤1:=hbH'.trans hH
  have he:=FirstGammaEndpointConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0 hb1 B hBDG q
  have hc:=FirstGammaConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap hH hH0 B hBDG θ q ((hqc.trans hcb).trans hbH)
  have hi (i:Fin ((n+n)+(n+n))) : stop 𝓕 μ H q (Rows i)=stop 𝓕 μ H q (PrefRows i) := by
    calc
      _=stop 𝓕 μ H q (stop 𝓕 μ H c (Rows i)):=by
        rw [StoppedInputAlgebra.stop_stop,min_eq_left (show (q:ℝ)≤(c:ℝ) by exact_mod_cast hqc)]
      _=_:=congrArg (stop 𝓕 μ H q)
        (FirstGammaEndpointCoherence.joint_stop 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ c hgap hcb i)
  filter_upwards [he,hc] with ω he hc
  rw [he,hc]
  apply PiLp.ext
  intro i
  simp only [StandardFiniteIto.vectorIntegral,WithLp.ofLp_toLp,hi i]

variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hH B hBDG hIJ₀ hIJ₁ hgap in
/-- The actual endpoint vector's current is literally the physical
corrected future mean on every covered positive-age prefix. -/
theorem current_eq_corrected (hb0 : 0<b) (hcb : c≤b) (q : ℝ≥0) (hvq : v≤q) (hqc : q≤c) :
    ∀ᵐ ω∂μ,∀ i,
      FirstGammaAffine.current n Λ θ (fun i=>(Z i).target) q (YE (q,ω)) i=
        functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
        θ*functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω)+
        θ*(Real.exp (-Λ*((Z i).target-(v:ℝ)))-Real.exp (-Λ*((q:ℝ)-(v:ℝ))))*
          functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω) := by
  filter_upwards [value_eq_prefix 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ c hgap hH B hBDG hb0 hcb q hqc,
    FirstGammaCurrentIdentity.current_eq_corrected 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap hH (hb0.trans_le hbH) B hBDG hIJ₀ hIJ₁ θ (hcb.trans hbH) q hvq hqc] with ω he hp i
  rw [he]
  exact hp i

end SHE.FirstGammaEndpointPhysical
