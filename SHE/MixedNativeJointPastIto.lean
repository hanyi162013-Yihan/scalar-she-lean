module

public import SHE.MixedNativeJointObservation
public import SHE.FiniteItoPastNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNativeJointPastIto
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open MixedNativeJointObservations
open scoped NNReal ENNReal
local instance mixedNativeJointPastIto_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeJointPastIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeJointPastIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeJointPastIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeJointPastIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeJointPastIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Ordinary finite-dimensional Itô applies directly to the actual
drift-cancelling joint observations, with their original separate stops
and targets. No additional formula or applicability assumption is used. -/
theorem finiteItoInput (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    {n : ℕ} (Z : Fin n→WordRecursion.Observation) (b : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(Z i).target) (hbH : b≤H)
    (v : ℝ≥0) (hvb : v≤b) :
    ∃ N : (ℝ→WordRecursion.State n→ℝ)→Ω→ℝ,
      (∀ G,Integrable (N G) μ ∧ ∀ A,MeasurableSet[𝓕 v] A → (∫ ω in A,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω t => value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b t.toNNReal ω)
        (StandardFiniteIto.rowCovariance 𝓕 μ H
          (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ)) v b N := by
  let Y := Function.uncurry (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
  let R := rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ
  have hY : StronglyMeasurable[𝓕.predictable] Y := predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH
  let N : (ℝ→WordRecursion.State n→ℝ)→Ω→ℝ := fun G ω =>
    FiniteItoNoise.noise 𝓕 μ H Y hY R J v b G ω
  refine ⟨N,fun G => ⟨FiniteItoNoise.noise_integrable 𝓕 μ H Y hY R J v b G,
    fun A hA => FiniteItoPastNoise.noise_centered_on_past_event 𝓕 μ H Y hY R J hlocal v b hvb G A hA⟩,?_⟩
  exact StandardFiniteIto.finiteItoInput 𝓕 μ H J hJ R (initial Λ u₀ v₀ Z) Y hY
    (continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
    (fun t _ => integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      Z b hgap hΛ hbH t) v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)

end SHE.MixedNativeJointPastIto
