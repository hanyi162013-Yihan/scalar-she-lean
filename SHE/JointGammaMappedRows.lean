module

public import SHE.JointGammaAffine
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

namespace SHE.JointGammaMappedRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaMappedRows_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaMappedRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaMappedRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaMappedRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaMappedRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaMappedRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaMappedRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaMappedRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

/-- The constant joint current only uses the actual current blocks;
its right coefficient is the ORIGINAL target damping. -/
theorem mapped_current {C : Type*} [AddCommGroup C] [Module ℝ C]
    (Q : Fin ((n+n)+(n+n))→C) (i : Fin n) :
    mappedRow L Q i=Q (Fin.castAdd (n+n) (Fin.castAdd n i))+
      (θ*Real.exp (-Λ*(Z i).target)) • Q (Fin.castAdd (n+n) (Fin.natAdd n i)) := by
  rw [JointGammaAffine.current,FiniteAffineRows.mapped_add,FiniteAffineRows.mapped_smul,
    FiniteAffineRows.mapped_terminal_comp,FiniteAffineRows.mapped_currentU,
    FiniteAffineRows.mapped_currentD,smul_smul]

/-- The SAME original finite-Itô rows, not new innovation rows, map to
literal terminal-damped current blocks throughout the open window. -/
theorem current_rows_ae : ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
    mappedRow L (fun j=>Rows j p) i=
      R (Fin.castAdd n i) p+(θ*Real.exp (-Λ*(Z i).target)) • R (Fin.natAdd n i) p := by
  filter_upwards [ae_all_iff.mpr (fun j=>StoppedItoInputs.stop_ae 𝓕 μ H (b:ℝ) (Raw j)),
    FiniteReferenceSplice.rows_after_past_ae 𝓕 μ H v R Rref] with p hs hp hvp hpb i
  have hbmem:p∈StoppedItoInputs.before (Ω:=Ω) (b:ℝ):=by exact_mod_cast hpb
  simp only [FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,hs,indicator_of_mem hbmem]
  rw [mapped_current]
  simp only [FiniteReferenceSplice.jointRows,Fin.append_left]

end SHE.JointGammaMappedRows

