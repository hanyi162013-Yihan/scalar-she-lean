module

public import SHE.JointGammaMappedRows
public import SHE.JointRescaledRows
public import SHE.FiniteReferenceSpliceRows
public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaEndpointCovariance
public import SHE.FiniteAffineRows
public import SHE.PredictableRealSections
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

namespace SHE.JointGammaPhysicalRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaPhysicalRows_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaPhysicalRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaPhysicalRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaPhysicalRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaPhysicalRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaPhysicalRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaPhysicalRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaPhysicalRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


open Set FiniteCovariancePullback
variable (θ : ℝ)
local notation "R" => FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH
local notation "Rref" => FirstGammaEndpointRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
local notation "Raw" => FiniteReferenceSplice.jointRows 𝓕 μ H v R Rref
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "Frozen" => fun i:Fin n=>TwoChannelItoRows.block 𝓕 μ H
  (FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH i)
  (FirstGammaEndpointRows.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ i)
local notation "L" => JointGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)

local notation "r0" => FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH
local notation "rU" => FirstGammaEndpointRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rV" => FirstGammaEndpointRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH

/-- Literal physical rows of the original joint finite martingale.
The residual interpolation retains exp[-Λ(target-currentTime)]. -/
theorem current_physical : ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
    mappedRow L (fun j=>Rows j p) i=
      WithLp.toLp 2 (r0 i p,(1-θ*Real.exp (-Λ*((Z i).target-(p.1:ℝ)))) • rU i p+
        (θ*Real.exp (-Λ*((Z i).target-(p.1:ℝ)))) • rV i p) := by
  have hi(i:Fin n):=JointRescaledRows.convex_ae 𝓕 μ H hΛ b (r0 i) (rU i) (rV i)
  filter_upwards [JointGammaMappedRows.current_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ,ae_all_iff.mpr hi]
    with p hm hi hvp hpb i
  rw [hm hvp hpb i]
  simpa only [FirstGammaEndpointRows.actual,Fin.append_left,Fin.append_right] using
    hi i hpb.le θ (Z i).target

end SHE.JointGammaPhysicalRows

