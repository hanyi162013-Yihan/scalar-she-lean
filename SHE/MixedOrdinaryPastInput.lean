module
public import SHE.ControlledOrdinaryPastInput
public import SHE.MixedNativeOrdinaryModel
public import SHE.MixedNativeRandomReferenceStep

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryPastInput
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedOrdinaryPastInput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedOrdinaryPastInput_sigma : MeasurableSpace CircleL2 := borel _
local instance mixedOrdinaryPastInput_borel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedOrdinaryPastInput_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedOrdinaryPastInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedOrdinaryPastInput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedOrdinaryPastInput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedOrdinaryPastInput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedOrdinaryPastInput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀z,ell≤aU z∧aU z≤M) (hbV : ∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
local notation "modelU" => MixedNativeOrdinaryModel.model 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
variable (P : CanonicalCovariance.ProfileParameters) (hAs : BoundedSmooth (fun z=>κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (hstop : ∀x,(Z.observations x 0).stop=(b:ℝ))
variable (htarget : ∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter : ∀x,(Z.observations x 0).center=x)
local notation "ht" => (fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,htarget] using (le_refl (b:ℝ)))
local notation "hs" => (fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hstop] using (le_refl (b:ℝ)))
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hIJ₀ hIJ₁ hnull hJ hstop htarget hcenter hsmall in
/-- Actual F_v past states and the actual rough first solution, with
the original J, native zero-gap root and both cutoffs removed. Only
the companion coefficient generating the reference words is smooth. -/
theorem original_input (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hbH : b≤H) (hvb' : v<b) (ν : Measure HeatCircle) [IsFiniteMeasure ν]
    (c : ℝ≥0) (hν : ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle)) (k : ℕ) :
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] fun ω=>
        ControlledOrdinaryAverage.average P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm modelU
          ν (pastParameter ω) k ω := by
  exact ControlledOrdinaryPastInput.random_input P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z hstop htarget hcenter F hF hFm modelU ν c hν hsmall hlocal hΛ hbH hvb' pastParameter
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v) k

end SHE.MixedOrdinaryPastInput
