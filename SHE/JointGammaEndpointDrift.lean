module

public import SHE.FirstGammaEndpointMappedRows
public import SHE.JointGammaDriftAlgebra
public import SHE.JointGammaTestFields
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

namespace SHE.JointGammaEndpointDrift
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointDrift_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointDrift_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointDrift_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointDrift_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointDrift_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointDrift_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointDrift_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointDrift_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable (θ : ℝ) (hvb : v≤b)
variable {F : WordRecursion.State n→ℝ} (hF : SmoothCylinders.BoundedSmooth F)
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => JointGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "G" => JointGammaTestFields.value P Λ θ v b hvb Z htarget F
local notation "dG" => JointGammaTestFields.derivative P Λ θ v b hvb Z htarget F

include hF in
/-- Exact cancellation for the original joint Gamma on one original
sample/time event, through the singular terminal target. -/
theorem actual_drift :
    ∀ᵐ ω∂μ,∀ᵐ t:ℝ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),∀ z,
      dG (Past ω) t z+(1/2:ℝ)*GaussianTaylorAverage.covarianceAction
        (StandardFiniteIto.rowCovariance 𝓕 μ H Rows ω t) (GaussianTaylor.hessian (G (Past ω) t) z)=
        (1/2:ℝ)*GaussianTaylorAverage.covarianceAction
          (gram (mappedRow L (fun j=>Rows j (t.toNNReal,ω)))-
            CovarianceMatrix.densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v (Past ω)) Z t)
          (GaussianTaylor.hessian (GaussianConvolution.gaussianAverage ((W (Past ω)).path t).val F) (L z)) := by
  have hr:=FirstGammaEndpointMappedRows.reference_gram_eq_profile 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ hvb
  filter_upwards [hr] with ω hr
  filter_upwards [hr] with t hr z
  exact JointGammaDriftAlgebra.cancellation P Λ θ v b hvb Z htarget hF (Past ω) t
    (fun j=>Rows j (t.toNNReal,ω)) z hr
end SHE.JointGammaEndpointDrift
