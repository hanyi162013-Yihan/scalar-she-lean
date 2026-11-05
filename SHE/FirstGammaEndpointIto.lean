module

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

namespace SHE.FirstGammaEndpointIto
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointIto_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointIto_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointIto_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance firstGammaEndpointIto_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance firstGammaEndpointIto_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance firstGammaEndpointIto_inputsBorel : BorelSpace ControlledProfile.Inputs := by
  dsimp [ControlledProfile.Inputs]
  infer_instance
local instance firstGammaEndpointIto_inputsSecondCountable : SecondCountableTopology ControlledProfile.Inputs := by
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

include B hBDG hF hsmall in
/-- Actual random-F_v Gaussian-comparison Itô THROUGH the singular
terminal heat endpoint, driven by the same original full-H integral.
True L² row energy proves all residual domination and past-event centering. -/
theorem formula (hb0 : 0<b) (hb1 : (b:ℝ)≤1) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) :
    ∃ Γ : Process (E:=Both RealHaarInput) 𝓕 μ H,
      Integrable (J.integral Γ) μ ∧
      (∀ A,MeasurableSet[𝓕 v] A→(∫ ω in A,J.integral Γ ω ∂μ)=0) ∧
      (∀ᵐ p∂energyMeasure μ H,Γ p=
        if v<p.1 ∧ p.1<b then FiniteItoNoise.gradientRow 𝓕 μ H (Y θ) (Rows) (G (Past p.2)) p else 0) ∧
      ∀ᵐ ω∂μ,G (Past ω) b (Y θ (b,ω))=
        G (Past ω) v (Y θ (v,ω))+J.integral Γ ω+
          ∫ t in (v:ℝ)..(b:ℝ),FiniteItoParameterResidual.drift (Y θ)
            (StandardFiniteIto.rowCovariance 𝓕 μ H (Rows)) (G) (dG) (Past ω) ω t := by
  have hYm:=FirstGammaEndpointConstruction.predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0 hb1 hnull B hBDG
  have hYc:=FirstGammaEndpointConstruction.continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0
  have hRep:=FirstGammaEndpointConstruction.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0 hb1 B hBDG
  have hgm:=FirstGammaTestFields.gradient_joint_measurable P Λ θ v b hvb Z htarget F hF hΛ
  have hpc (t:ℝ) (z:FirstGammaAffine.Space n) : Continuous (fun p:Inputs=>fderiv ℝ (G p t) z) := by
    have hh:=FirstGammaParameterDerivatives.gradient_parameter_continuous P hΛ θ v b hvb Z htarget hF hsmall t
    have hmap : Continuous (fun p:Inputs=>(p,z)):=continuous_id.prodMk continuous_const
    have hr:=hh.comp hmap
    exact hr
  have hs:=FirstGammaTestFields.uniformSmooth P Λ θ v b hvb Z htarget F hF hΛ
  obtain ⟨L,hL0,hL⟩:=hs.fderiv.norm_bound
  have hLb : ∀ p t z,‖fderiv ℝ (G p t) z‖≤L:=fun p t z=>hL (p,t) z
  obtain ⟨Q,hQ0,hQ⟩:=hs.fderiv.fderiv.norm_bound
  have hQb : ∀ p t z,‖GaussianTaylor.hessian (G p t) z‖≤Q:=fun p t z=>hQ (p,t) z
  have hreg (p:Inputs) : LocalizedItoTest.SmoothTimeTest v b (G p) (dG p) :=
    FirstGammaTestFields.smoothTimeTest P Λ θ v b hvb Z htarget F hF hΛ p
  obtain ⟨m,hm,hm0,hmb⟩:=FirstGammaDerivativeEnvelope.uniform_envelope P hΛ θ v b hvb Z htarget hF
  have hmpos : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),0≤m t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hm0 t ht
  have hmbd (p:Inputs) : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),∀ z,‖dG p t z‖≤m t*(1+‖z‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne z
    exact hmb p t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩ z
  have hdp : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),Continuous
      (fun p:Inputs×FirstGammaAffine.Space n=>dG p.1 t p.2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    exact FirstGammaParameterDerivatives.derivative_parameter_continuous P hΛ θ v b hvb Z htarget hF hsmall
      (lt_of_le_of_ne ht.2 hne)
  have hpast:=MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  let inp:=FiniteItoBorelGradient.input 𝓕 μ H (Y θ) hYm (Rows) (G) hgm L hL0 hLb v b (0:Inputs) hpast
  have hc:=FiniteItoRandomCentering.centered 𝓕 μ H (Y θ) hYm (Rows) (G) hgm L hL0 hLb v b (0:Inputs) J hlocal hpast
  refine ⟨inp,hc.1,hc.2,FiniteItoBorelGradient.input_ae 𝓕 μ H (Y θ) hYm (Rows) (G) hgm L hL0 hLb v b (0:Inputs) hpast,?_⟩
  exact FiniteItoEnergyAnalytic.formula 𝓕 μ H (Y θ) hYm (Rows) J (G) (dG) hgm hpc L hL0 hLb v b (0:Inputs)
    hJ hlocal (FiniteReferenceSplice.jointInitial z₀) hYc (fun t _=>hRep t) hvb hbH hreg
    (FirstGammaTestFields.value_parameter_continuous P Λ θ v b hvb Z htarget F hF hΛ hsmall)
    (FirstGammaParameterDerivatives.hessian_parameter_continuous P hΛ θ v b hvb Z htarget hF hsmall)
    hdp Q hQ0 hQb m hm hmpos hmbd hpast.stronglyMeasurable

end SHE.FirstGammaEndpointIto
