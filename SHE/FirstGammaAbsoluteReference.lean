module

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

namespace SHE.FirstGammaAbsoluteReference
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaAbsoluteReference_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaAbsoluteReference_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaAbsoluteReference_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaAbsoluteReference_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaAbsoluteReference_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaAbsoluteReference_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaAbsoluteReference_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaAbsoluteReference_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable (hΛ : 0≤Λ) (v c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)


open FirstGammaConstruction
local notation "Rold" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "Rnew" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap
local notation "z₀" => MixedNativePairExtendedMartingale.initial u₀ v₀ (fun i=>(Z i).target) (fun i=>(Z i).center)
local notation "Y" => FirstGammaConstruction.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
variable (hH : (H:ℝ)≤1) (hH0 : 0<H) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 J B)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

attribute [local irreducible] FirstGammaConstruction.value FirstGammaRows.replacement

include hH hH0 B hBDG hIJ₀ hIJ₁ in
/-- The literal absolute finite reference retains its full target and
its same-J post-past frozen noise, rather than only identifying a
difference of two references. -/
theorem reference_absolute (θ : ℝ) (hcH : c≤H) (hvc : v≤c) :
    ∀ᵐ ω∂μ,∀ i,
      FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target) (Y θ (c,ω)) i=
        functional ((Z i).target-(v:ℝ)) (Z i).center (S.first v ω)+
        θ*Real.exp (-Λ*((Z i).target-(v:ℝ)))*
          functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)+
        J.integral (StoppedItoInputs.stop 𝓕 μ H (c:ℝ)
          (PastItoInputs.post 𝓕 μ H v (Rnew θ (Fin.castAdd n i)))) ω := by
  have hr:=FirstGammaFrozenValues.right_eq_reference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH c hvc le_rfl
  have hd:=FirstGammaFrozenValues.pastD_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z J P hκP hΛ v c hgap
    hH hH0 B hBDG hIJ₀ hIJ₁ θ hcH c hvc le_rfl
  filter_upwards [hr,hd] with ω hr hd i
  have h0:=congrArg (fun z:WordRecursion.State (n+n)=>z (Fin.castAdd n i)) hr
  simp only [PiLp.add_apply,WithLp.ofLp_toLp] at h0
  rw [FirstGammaAffine.reference_apply,hd i]
  change (FiniteComparisonTest.right (n+n) (Y θ (c,ω))) (Fin.castAdd n i)+
    θ*Real.exp (-Λ*(Z i).target)*(Real.exp (Λ*(v:ℝ))*
      functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω))=_
  rw [h0]
  have he:Real.exp (-Λ*(Z i).target)*Real.exp (Λ*(v:ℝ))=
      Real.exp (-Λ*((Z i).target-(v:ℝ))):=by rw [←Real.exp_add];congr 1;ring
  simp only [MixedNativePairExtendedMartingale.value,WithLp.ofLp_toLp,Fin.append_left,min_eq_left hvc]
  rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _
    (sub_le_sub_left (show (v:ℝ)≤(c:ℝ) by exact_mod_cast hvc) _)]
  simp only [Function.uncurry]
  calc
    _=functional ((Z i).target-(v:ℝ)) (Z i).center (S.first v ω)+
      θ*(Real.exp (-Λ*(Z i).target)*Real.exp (Λ*(v:ℝ)))*
        functional ((Z i).target-(v:ℝ)) (Z i).center (S.second v ω-S.first v ω)+
      J.integral (StoppedItoInputs.stop 𝓕 μ H (c:ℝ)
        (PastItoInputs.post 𝓕 μ H v (Rnew θ (Fin.castAdd n i)))) ω:=by ring
    _=_:=by rw [he]

end SHE.FirstGammaAbsoluteReference


