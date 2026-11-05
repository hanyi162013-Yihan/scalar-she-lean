module

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
public import SHE.FirstGammaTestFields
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

namespace SHE.FirstGammaEndpointIdentity
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointIdentity_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointIdentity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointIdentity_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointIdentity_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointIdentity_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointIdentity_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance firstGammaEndpointIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance firstGammaEndpointIdentity_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance firstGammaEndpointIdentity_inputsBorel : BorelSpace ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
local instance firstGammaEndpointIdentity_inputsSecondCountable : SecondCountableTopology ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
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


local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaEndpointConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH
variable (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)

open Set ControlledProfile UniformSmooth SmoothCylinders
variable (hvb : v≤b)
variable {F : WordRecursion.State n→ℝ} (hF : BoundedSmooth F)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (θ : ℝ)
local notation "G" => FirstGammaTestFields.value P Λ θ v b hvb Z htarget F
local notation "dG" => FirstGammaTestFields.derivative P Λ θ v b hvb Z htarget F
local notation "Rows" => FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open FiniteCovariancePullback FiniteMappedGradient
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => FirstGammaAffine.current n Λ θ (fun i=>(Z i).target)
local notation "Ref" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)
local notation "Fbar" => fun p:ℝ≥0×Ω=>GaussianConvolution.gaussianAverage ((W (Past p.2)).path (p.1:ℝ)).val F
local notation "Rcur" => fun p:ℝ≥0×Ω=>mappedRow (L (p.1:ℝ)) (fun j=>Rows j p)
local notation "Rref" => fun p:ℝ≥0×Ω=>mappedRow Ref (fun j=>Rows j p)

def completeNoise (p : ℝ≥0×Ω) : Both RealHaarInput:=
  contract (fderiv ℝ (Fbar p) (L (p.1:ℝ) (Y θ p))) (fun i=>Rcur p i-Rref p i)+
    contract (fderiv ℝ (Fbar p) (L (p.1:ℝ) (Y θ p))-
      fderiv ℝ (Fbar p) (Ref (Y θ p))) (Rref p)

def retained (ω : Ω) (t : ℝ) : ℝ :=
  fderiv ℝ (GaussianConvolution.gaussianAverage ((W (Past ω)).path t).val F)
    (L t (Y θ (t.toNNReal,ω)))
    (FirstGammaAffine.currentDerivative n Λ θ t (Y θ (t.toNNReal,ω)))+
    (1/2:ℝ)*GaussianTaylorAverage.covarianceAction
      (gram (mappedRow (L t) (fun j=>Rows j (t.toNNReal,ω)))-
        CovarianceMatrix.densityMatrix (ControlledReferenceWindows.coefficient P Λ θ v (Past ω)) Z t)
      (GaussianTaylor.hessian (GaussianConvolution.gaussianAverage ((W (Past ω)).path t).val F)
        (L t (Y θ (t.toNNReal,ω))))

include hF in
theorem noise_decomposition (p : ℝ≥0×Ω) :
    FiniteItoNoise.gradientRow 𝓕 μ H (Y θ) Rows (G (Past p.2)) p=
      completeNoise (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb θ p := by
  have hs : SmoothCylinders.BoundedSmooth (Fbar p):=
    hF.average (ProbabilityTheory.multivariateGaussian (0:WordRecursion.State n)
      ((W (Past p.2)).path (p.1:ℝ)).val)
  have he : G (Past p.2) (p.1:ℝ)=(fun z=>Fbar p (L (p.1:ℝ) z)-Fbar p (Ref z)) := by
    funext z
    exact FirstGammaTestFields.value_apply P Λ θ v b hvb Z htarget F (Past p.2) p.1 z
  change contract (fderiv ℝ (G (Past p.2) (p.1:ℝ)) (Y θ p)) (fun j=>Rows j p)=_
  rw [he,paired_gradient (L (p.1:ℝ)) Ref hs,complete]
  rfl

include B hBDG hF hsmall in
/-- Complete centered first-Gamma identity for actual random-past
observations THROUGH the terminal heat endpoint. BOTH martingale
terms and the retained control drift are explicit. -/
theorem formula (hb0 : 0<b) (hb1 : (b:ℝ)≤1)
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) :
    ∃ Γ : Process (E:=Both RealHaarInput) 𝓕 μ H,
      Integrable (J.integral Γ) μ ∧
      (∀ A,MeasurableSet[𝓕 v] A→(∫ ω in A,J.integral Γ ω ∂μ)=0) ∧
      (∀ᵐ p∂energyMeasure μ H,Γ p=if v<p.1 ∧ p.1<b then
        completeNoise (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb θ p else 0) ∧
      ∀ᵐ ω∂μ,F (L b (Y θ (b,ω)))-F (Ref (Y θ (b,ω)))=J.integral Γ ω+
        ∫ t in (v:ℝ)..(b:ℝ),retained (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb θ ω t := by
  obtain ⟨Γ,hint,hcenter,hΓ,hformula⟩:=FirstGammaEndpointIto.formula 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH B hBDG hvb hF hsmall θ hb0 hb1 hnull hJ hlocal
  have hinit:=FirstGammaEndpointValues.initial_zero (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH B hBDG hvb θ hb0 hb1
  have hd:=FirstGammaEndpointDrift.actual_drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ hvb hF
  refine ⟨Γ,hint,hcenter,?_,?_⟩
  · filter_upwards [hΓ] with p hp
    rw [hp,noise_decomposition 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb hF θ p]
  · filter_upwards [hformula,hinit,hd] with ω hf hi hd
    rw [FirstGammaEndpointValues.terminal_value (F:=F) 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hvb θ ω,hi,zero_add] at hf
    rw [hf]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)]
    filter_upwards [hd] with t ht
    exact ht (Y θ (t.toNNReal,ω))

end SHE.FirstGammaEndpointIdentity
