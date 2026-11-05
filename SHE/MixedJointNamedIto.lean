module

public import SHE.MixedNativeJointObservation
public import SHE.MixedNativePastBackwardStep

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedJointNamedIto
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


variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ)
variable {n:ℕ} (Z:Fin n→WordRecursion.Observation) (b:ℝ≥0)
variable (hgap:∀i,(b:ℝ)<(Z i).target) (hbH:b≤H)

def path:ℝ≥0×Ω→WordRecursion.State n:=
  Function.uncurry (value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)

def scalarNoise (v:ℝ≥0) (G:ℝ→WordRecursion.State n→ℝ):Lp ℝ 2 μ:=
  FiniteItoNoise.noise 𝓕 μ H (path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
    (predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH)
    (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ) J v b G

include hIJ₀ hIJ₁ in
/-- The ordinary finite-dimensional formula with the ORIGINAL named
scalar integral as noise, rather than an opaque existential witness. -/
theorem finite_ito (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (v:ℝ≥0) (hvb:v≤b):
    PhysicalIto.FiniteItoInput μ
      (fun ω t=>path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b (t.toNNReal,ω))
      (StandardFiniteIto.rowCovariance 𝓕 μ H
        (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ)) v b
      (fun G ω=>scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ Z b hgap hbH v G ω):=by
  exact StandardFiniteIto.finiteItoInput 𝓕 μ H J hJ
    (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ)
    (initial Λ u₀ v₀ Z)
    (path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
    (predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH)
    (continuous_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
    (fun t _=>integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      Z b hgap hΛ hbH t) v.2 (by exact_mod_cast hvb) (by exact_mod_cast hbH)

/-- Every admissible named noise is exactly the same original J
applied to the stopped full physical gradient row. -/
theorem noise_eq_integral (v:ℝ≥0) (G:ℝ→WordRecursion.State n→ℝ)
    (hG:FiniteItoNoise.AdmissibleGradient G):
    scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ Z b hgap hbH v G=
      J.integral (
        StoppedItoInputs.stop 𝓕 μ H b (FiniteItoNoise.gradientProcess 𝓕 μ H
          (path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
          (predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH)
          (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ) G hG)-
        StoppedItoInputs.stop 𝓕 μ H v (FiniteItoNoise.gradientProcess 𝓕 μ H
          (path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b)
          (predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH)
          (rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ) G hG)):=by
  exact FiniteItoNoise.noise_eq 𝓕 μ H _ _ _ J v b G hG

/-- Its centering on past events is derived from ordinary locality of
that very same full-horizon integral. -/
theorem noise_on_past_event (hlocal:StandardTerminalPastLocality J)
    (v:ℝ≥0) (hvb:v≤b) (G:ℝ→WordRecursion.State n→ℝ) (A:Set Ω)
    (hA:MeasurableSet[𝓕 v] A):
    (∫ω in A,scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ Z b hgap hbH v G ω ∂μ)=0:=by
  exact FiniteItoPastNoise.noise_centered_on_past_event 𝓕 μ H _ _ _ J hlocal v b hvb G A hA

end SHE.MixedJointNamedIto
