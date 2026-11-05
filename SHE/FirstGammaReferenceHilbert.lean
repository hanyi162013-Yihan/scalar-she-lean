module

public import SHE.FirstGammaFrozenDifference
public import SHE.PastReferenceScalarStopped
public import SHE.MixedPastReferenceDampedMoment
public import SHE.FirstGammaFrozenValues
public import SHE.FirstGammaEndpointPhysical
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.FirstGammaRows
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaValues
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

namespace SHE.FirstGammaReferenceHilbert
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaFrozenValues_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaFrozenValues_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaFrozenValues_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaFrozenValues_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaFrozenValues_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaFrozenValues_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaFrozenValues_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)


open FirstGammaConstruction
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ u₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z J P hκP hΛ v c hgap
variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))



local notation "Data"=>MixedPastReference.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
local notation "DataM"=>MixedPastReference.data_past_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S v
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hvc:v<c) (hcH:c≤H) (hspan:(c:ℝ)-(v:ℝ)≤P.horizon)
variable (Bpast:ℝ≥0) (hBDGpast:StandardTerminalBDGPower 2 J Bpast)
local notation "hv1"=>(show (v:ℝ)≤1 from
  (show (v:ℝ)≤(H:ℝ) from by exact_mod_cast hvc.le.trans hcH).trans hH)
local notation "Inp" "[" θ "," η "]"=>MixedPastReference.input
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
  P hΛ hκP θ η hsmall v c hvc hcH hv1 hspan 1 (by norm_num) Bpast hBDGpast

attribute [local irreducible] FirstGammaConstruction.value FirstGammaRows.replacement MixedPastReference.input

include hH hH0 B hBDG hIJ₀ hIJ₁ in
/-- The ACTUAL finite reference difference is the original damped past
heat observation plus a positive-age observation of the SAME original
Hilbert frozen-difference integral. Predictability, finite input energy,
all scalar/Hilbert compatibility and additive cancellation are derived. -/
theorem reference_difference (θ η:ℝ):
    ∀ᵐω ∂μ,∀i:Fin n,
      FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target) (Y θ (c,ω)) i-
      FirstGammaAffine.reference n Λ η (fun i=>(Z i).target) (Y η (c,ω)) i=
        (θ-η)*Real.exp (-Λ*((Z i).target-(v:ℝ)))*
          functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)+
        functional ((Z i).target-(c:ℝ)) (Z i).center (I₁.integral (Inp[θ,η]) ω):=by
  have hd:=MixedPastReference.data_moments 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hΛ v (hvc.le.trans hcH) hv1 (p:=1) (by norm_num) Bpast hBDGpast
  have hn(i:Fin n):
      (fun ω=>functional ((Z i).target-(c:ℝ)) (Z i).center (I₁.integral (Inp[θ,η]) ω))=ᵐ[μ]
      (fun ω=>J.integral (StoppedItoInputs.stop 𝓕 μ H c
        (PastItoInputs.post 𝓕 μ H v (Rnew θ (Fin.castAdd n i)))) ω-
       J.integral (StoppedItoInputs.stop 𝓕 μ H c
        (PastItoInputs.post 𝓕 μ H v (Rnew η (Fin.castAdd n i)))) ω):=by
    let A:=NativeObservationProcess.process 𝓕 μ H hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (hgap i) (Z i).center
    have he:=PastReferenceScalarStopped.observe_two_channel 𝓕 μ P hΛ hκP θ η hsmall
      H v c hvc hcH hspan Data DataM hd.1 I₁ J hIJ₁ A (Z i).target (hgap i) (Z i).center
    convert! he using 1 <;>
      simp only [MixedPastReference.input,FirstGammaRows.replacement,Fin.append_left,
        PastFrozenPrefixRows.rows,PastReferenceScalarObservation.row,
        MixedPastReference.data,MixedNativeFrozenPrefixIto.data,A] <;> rfl
  have hf:=FirstGammaFrozenDifference.reference_difference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hIJ₀ hIJ₁ θ η hcH hvc.le
  filter_upwards [hf,ae_all_iff.mpr hn] with ω hf hn i
  exact (hf i).trans (congrArg (fun z:ℝ=>(θ-η)*Real.exp (-Λ*((Z i).target-(v:ℝ)))*
    functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)+z) (hn i).symm)

end SHE.FirstGammaReferenceHilbert
