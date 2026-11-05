module

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

namespace SHE.FirstGammaEndpointMappedRows
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointMappedRows_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointMappedRows_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointMappedRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointMappedRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointMappedRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointMappedRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointMappedRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointMappedRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local notation "L" => FirstGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)

/-- The singular full-H reference rows are the literal frozen rows on
one original energy event throughout the OPEN physical window. -/
theorem reference_rows_ae : ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
    mappedRow Ref (fun j=>Rows j p) i=Frozen i p := by
  filter_upwards [ae_all_iff.mpr (fun j=>StoppedItoInputs.stop_ae 𝓕 μ H (b:ℝ) (Raw j)),
    FiniteReferenceSplice.rows_after_past_ae 𝓕 μ H v R Rref,
    ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hs hp hz hvp hpb i
  have hbmem : p∈StoppedItoInputs.before (Ω:=Ω) (b:ℝ):=by exact_mod_cast hpb
  simp only [FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,hs,indicator_of_mem hbmem]
  rw [FiniteAffineRows.mapped_reference]
  simp only [FiniteReferenceSplice.jointRows,Fin.append_right]
  rw [hp hvp (Fin.castAdd n i),hp hvp (Fin.natAdd n i)]
  simp only [FirstGammaEndpointRows.replacement,Fin.append_left,Fin.append_right,hz,Pi.zero_apply,smul_zero,add_zero]

theorem current_rows_ae : ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀ i,
    mappedRow (L (p.1:ℝ)) (fun j=>Rows j p) i=
      R (Fin.castAdd n i) p+ClippedExponential.coefficient Λ θ (p.1:ℝ) • R (Fin.natAdd n i) p := by
  filter_upwards [ae_all_iff.mpr (fun j=>StoppedItoInputs.stop_ae 𝓕 μ H (b:ℝ) (Raw j)),
    FiniteReferenceSplice.rows_after_past_ae 𝓕 μ H v R Rref,
    ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hs hp hz hvp hpb i
  have hbmem : p∈StoppedItoInputs.before (Ω:=Ω) (b:ℝ):=by exact_mod_cast hpb
  simp only [FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,hs,indicator_of_mem hbmem]
  rw [FiniteAffineRows.mapped_current]
  simp only [FiniteReferenceSplice.jointRows,Fin.append_left,Fin.append_right]
  rw [hp hvp (Fin.natAdd n i)]
  simp only [FirstGammaEndpointRows.replacement,Fin.append_right,hz,Pi.zero_apply,smul_zero,add_zero]

/-- Actual transformed reference Gram equals TOTAL canonical profile
density THROUGH the terminal window, with no positive-gap premise. -/
theorem reference_gram_eq_profile (hvb : v≤b) :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),
      gram (mappedRow Ref (fun j=>Rows j (t.toNNReal,ω)))=
        CovarianceMatrix.densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v
          (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) Z t := by
  have hr:=PredictableRealSections.of_energy_ae μ H
    (reference_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ)
    v b v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)
  have hc:=FirstGammaEndpointCovariance.frozen_covariance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
  filter_upwards [hr,hc] with ω hr hc
  filter_upwards [hr,hc,ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t hr hc ht hne
  have ht0 : 0≤t:=v.2.trans ht.1.le
  have htv : v<t.toNNReal:=by
    change (v:ℝ)<(t.toNNReal:ℝ)
    rw [Real.coe_toNNReal _ ht0]
    exact ht.1
  have htb : t.toNNReal<b:=by
    change (t.toNNReal:ℝ)<(b:ℝ)
    rw [Real.coe_toNNReal _ ht0]
    exact lt_of_le_of_ne ht.2 hne
  ext i j
  change inner ℝ (mappedRow Ref (fun j=>Rows j (t.toNNReal,ω)) i)
    (mappedRow Ref (fun j=>Rows j (t.toNNReal,ω)) j)=_
  rw [hr htv htb i,hr htv htb j]
  exact congrArg (fun A:Matrix (Fin n) (Fin n) ℝ=>A i j) hc

end SHE.FirstGammaEndpointMappedRows
