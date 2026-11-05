module

public import SHE.JointGammaCurrentIdentity
public import SHE.AEContinuousVersion
public import SHE.JointInterpolationFields
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

namespace SHE.JointGammaCurrentTime
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance jointGammaCurrentTime_realSigma : MeasurableSpace RealL2 := borel _
local instance jointGammaCurrentTime_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance jointGammaCurrentTime_circleSigma : MeasurableSpace CircleL2 := borel _
local instance jointGammaCurrentTime_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance jointGammaCurrentTime_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance jointGammaCurrentTime_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance jointGammaCurrentTime_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance jointGammaCurrentTime_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

local instance jointGammaCurrentTime_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance jointGammaCurrentTime_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance jointGammaCurrentTime_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
attribute [local irreducible] functional FirstGammaEndpointConstruction.value

include hH B hBDG hIJ₀ hIJ₁ in
/-- For EVERY original finite observation, the joint current identity
holds on the genuine original time/sample measure, not just at fixed times. -/
theorem current_eq_joint_time (hb0:0<b) (θ:ℝ):
    ∀ᵐ p∂energyMeasure μ H,v<p.1→p.1<b→∀i,
      JointGammaAffine.current n Λ θ (fun i=>(Z i).target) (Y θ p) i=
        functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.first p.1 p.2)+
          θ*Real.exp (-Λ*((Z i).target-(p.1:ℝ)))*
            functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.second p.1 p.2-S.first p.1 p.2):=by
  have hu:Measurable (Function.uncurry S.first):=
    (S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hv:Measurable (Function.uncurry S.second):=
    (S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  have hall(i:Fin n):∀ᵐp∂energyMeasure μ H,v<p.1→p.1<b→
      JointGammaAffine.current n Λ θ (fun i=>(Z i).target) (Y θ p) i=
        functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.first p.1 p.2)+
          θ*Real.exp (-Λ*((Z i).target-(p.1:ℝ)))*
            functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.second p.1 p.2-S.first p.1 p.2):=by
    let u:ℝ≥0→Ω→ℝ:=fun q ω=>JointGammaAffine.current n Λ θ (fun i=>(Z i).target) (Y θ (q,ω)) i
    let f:ℝ≥0×Ω→ℝ:=fun p=>
      functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.first p.1 p.2)+
        θ*Real.exp (-Λ*((Z i).target-(p.1:ℝ)))*
          functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.second p.1 p.2-S.first p.1 p.2)
    have ht:Measurable (fun p:ℝ≥0×Ω=>(Z i).target-(p.1:ℝ)):=
      measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst)
    have hf0:Measurable (fun p:ℝ≥0×Ω=>functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.first p.1 p.2)):=
      functional_joint_measurable.comp (hu.prodMk (ht.prodMk measurable_const))
    have hf1:Measurable (fun p:ℝ≥0×Ω=>functional ((Z i).target-(p.1:ℝ)) (Z i).center (S.second p.1 p.2-S.first p.1 p.2)):=
      functional_joint_measurable.comp ((hv.sub hu).prodMk (ht.prodMk measurable_const))
    have hf:Measurable f:=hf0.add ((((ht.const_mul (-Λ)).exp).const_mul θ).mul hf1)
    have hc(ω:Ω):Continuous (fun q:Set.Ioo v b=>u q ω):=by
      have hY:=FirstGammaEndpointConstruction.continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH θ hb0 ω
      exact (EuclideanSpace.proj i).continuous.comp
        ((JointGammaAffine.current n Λ θ (fun i=>(Z i).target)).continuous.comp
          (hY.comp continuous_subtype_val))
    have hs(q:ℝ≥0)(hq:q∈Set.Ioo v b):u q=ᵐ[μ] fun ω=>f (q,ω):=by
      filter_upwards [JointGammaCurrentIdentity.current_eq_joint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ v₀ S Z J P hκP hΛ v b htarget hbH hH B hBDG hIJ₀ hIJ₁ θ q hq.2] with ω hω
      exact hω i
    have he:=AEContinuousSections.ae_eq_version_on (timeMeasure H) μ (Set.Ioo v b) measurableSet_Ioo u f hc hf hs
    rw [Measure.restrict_prod_eq_prod_univ] at he
    have he':=ae_imp_of_ae_restrict he
    exact he'.mono (fun p hp hvp hpb=>hp ⟨⟨hvp,hpb⟩,Set.mem_univ _⟩)
  filter_upwards [ae_all_iff.mpr hall] with p hp hvp hpb i
  exact hp i hvp hpb

end SHE.JointGammaCurrentTime
