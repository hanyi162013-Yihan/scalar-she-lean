module

public import SHE.JointGammaTestFields
public import SHE.JointGammaPhysicalRows
public import SHE.ScalarGaussianProjection
public import SHE.FirstGammaEndpointIdentity
public import SHE.FirstGammaEndpointRowBounds
public import SHE.FirstGammaEndpointIto
public import SHE.FirstGammaEndpointValues
public import SHE.FirstGammaEndpointDrift
public import SHE.FiniteMappedGradient
public import SHE.FirstGammaEndpointConstruction
public import SHE.FiniteItoEnergyAnalytic
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.JointGammaTestFields
public import SHE.FirstGammaParameterDerivatives
public import SHE.FirstGammaDerivativeEnvelope
public import SHE.FiniteItoSmoothAnalytic
public import SHE.FiniteItoRandomCentering
public import SHE.SmoothTimeTestRestriction
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

namespace SHE.JointGammaScalarNoise
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaScalarNoise_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaScalarNoise_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaScalarNoise_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaScalarNoise_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaScalarNoise_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaScalarNoise_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaScalarNoise_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaScalarNoise_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance jointGammaScalarNoise_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance jointGammaScalarNoise_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance jointGammaScalarNoise_inputsBorel : BorelSpace ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
local instance jointGammaScalarNoise_inputsSecondCountable : SecondCountableTopology ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (Z : Fin 1→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH
variable (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)

open Set ControlledProfile UniformSmooth SmoothCylinders
variable (hvb : v≤b)
variable (a : ℝ→ℝ) (ha : BoundedSmooth a)
local notation "RootTest" => (fun z : WordRecursion.State 1=>a (z 0))
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (θ : ℝ)
local notation "G" => JointGammaTestFields.value P Λ θ v b hvb Z htarget RootTest
local notation "dG" => JointGammaTestFields.derivative P Λ θ v b hvb Z htarget RootTest
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open FiniteCovariancePullback FiniteMappedGradient
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => JointGammaAffine.current 1 Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference 1 Λ θ (fun i=>(Z i).target)
local notation "Fbar" => fun p:ℝ≥0×Ω=>GaussianConvolution.gaussianAverage ((W (Past p.2)).path (p.1:ℝ)).val RootTest
local notation "Rcur" => fun p:ℝ≥0×Ω=>mappedRow L (fun j=>Rows j p)
local notation "Rref" => fun p:ℝ≥0×Ω=>mappedRow Ref (fun j=>Rows j p)

local notation "σ" p => (((W (Past p.2)).path (p.1:ℝ)).val 0 0).toNNReal
local notation "gradient" => (fun (p : ℝ≥0×Ω) (z : ℝ)=>deriv (ScalarGaussianSemigroup.heat (σ p) a) z)

def noise (p:ℝ≥0×Ω):Both RealHaarInput:=
  FiniteItoNoise.gradientRow 𝓕 μ H (Y θ) (Rows) (G (Past p.2)) p

include ha in
/-- The ORIGINAL finite-Itô joint comparison gradient row is exactly
the full current-row minus frozen-row scalar Gaussian gradient. -/
theorem noise_scalar (p:ℝ≥0×Ω):
    noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb a θ p=
      gradient p (L (Y θ p) 0) • Rcur p 0-gradient p (Ref (Y θ p) 0) • Rref p 0 := by
  have hroot : BoundedSmooth RootTest := ha.comp_right (EuclideanSpace.proj (0:Fin 1))
  have hs:BoundedSmooth (Fbar p):=hroot.average
    (ProbabilityTheory.multivariateGaussian (0:WordRecursion.State 1) ((W (Past p.2)).path (p.1:ℝ)).val)
  have he:G (Past p.2) (p.1:ℝ)=(fun z=>Fbar p (L z)-Fbar p (Ref z)):=by
    funext z
    exact JointGammaTestFields.value_apply P Λ θ v b hvb Z htarget RootTest (Past p.2) p.1 z
  change contract (fderiv ℝ (G (Past p.2) (p.1:ℝ)) (Y θ p)) (fun j=>Rows j p)=_
  rw [he,FiniteMappedGradient.paired_gradient L Ref hs]
  simp only [contract,Fin.sum_univ_one]
  rw [ScalarGaussianProjection.fderiv (((W (Past p.2)).path (p.1:ℝ)).property) 0 a ha,
    ScalarGaussianProjection.fderiv (((W (Past p.2)).path (p.1:ℝ)).property) 0 a ha]
  simp only [EuclideanSpace.basisFun_apply,PiLp.single_apply,ite_true,mul_one]

local notation "r0" => FirstGammaEndpointRows.additive 𝓕 μ H κ hκ Z b htarget hbH
local notation "rU" => FirstGammaEndpointRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rV" => FirstGammaEndpointRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH
local notation "rF" => FirstGammaEndpointRows.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ

include ha in
/-- Literal complete JOINT Gamma noise on its strict physical window.
The convex remaining-target weight is retained inside the original row. -/
theorem noise_physical : ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→
    noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb a θ p=
      gradient p (L (Y θ p) 0) • WithLp.toLp 2
        (r0 0 p,(1-θ*Real.exp (-Λ*((Z 0).target-(p.1:ℝ)))) • rU 0 p+
          (θ*Real.exp (-Λ*((Z 0).target-(p.1:ℝ)))) • rV 0 p)-
      gradient p (Ref (Y θ p) 0) • WithLp.toLp 2 (r0 0 p,rF 0 p) := by
  filter_upwards [JointGammaPhysicalRows.current_physical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ,
    FirstGammaEndpointMappedRows.reference_rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ,
    TwoChannelItoRows.block_ae 𝓕 μ H (r0 0) (rF 0)] with p hc hr hb hvp hpb
  rw [noise_scalar 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb a ha θ p]
  change gradient p (L (Y θ p) 0) • mappedRow L (fun j=>Rows j p) 0-
    gradient p (Ref (Y θ p) 0) • mappedRow Ref (fun j=>Rows j p) 0=_
  rw [hc hvp hpb 0,(hr hvp hpb 0).trans hb]

end SHE.JointGammaScalarNoise

