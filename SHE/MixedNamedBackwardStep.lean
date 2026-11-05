module

public import SHE.MixedJointNamedIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.MixedNamedBackwardStep
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianItoTest GaussianTaylor GaussianTaylorAverage CovarianceEndpoint
open scoped NNReal ENNReal
local instance mixedNativePastBackwardStep_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativePastBackwardStep_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativePastBackwardStep_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativePastBackwardStep_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativePastBackwardStep_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativePastBackwardStep_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

theorem cancellation {n : ℕ} (W : EndpointWindow n) (F : State n→ℝ)
    (Γ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (z : State n) :
    backwardDerivative W F t z+(1/2:ℝ)*covarianceAction Γ (hessian (backward W F t) z)=
      (1/2:ℝ)*covarianceAction (Γ-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
        (hessian (backward W F t) z) := by
  rw [NativeControlledGenerator.covarianceAction_sub]
  unfold backwardDerivative
  ring

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
/-- The actual joint backward identity with its FULL original stopped
gradient scalar integral named explicitly. This applies to every finite
recursive test before its original stops, not just the leading root. -/
theorem formula (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hΛ:0≤Λ)
    {n:ℕ} (W:EndpointWindow n) (v:ℝ≥0) (hleft:W.left=(v:ℝ))
    (b:ℝ≥0) (hW:W.right=(b:ℝ)) (hbH:b≤H)
    (hgap:∀i,(b:ℝ)<(W.observations i).target)
    {F:State n→ℝ} (hF:BoundedSmooth F):
    let Y:=fun (ω:Ω) (t:ℝ)=>MixedNativeJointObservations.value
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W.observations b t.toNNReal ω
    let R:=MixedNativeJointObservations.rows
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W.observations b hgap hΛ
    ∀ᵐω∂μ,F (Y ω b)=WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F (Y ω W.left)+
      MixedJointNamedIto.scalarNoise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        J hIJ₀ hIJ₁ hnull hΛ W.observations b hgap hbH v (backward W F) ω+
      ∫t in W.left..W.right,(1/2:ℝ)*covarianceAction
        (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
        (hessian (backward W F t) (Y ω t)):=by
  intro Y R
  have hvb:v≤b:=by exact_mod_cast (show (v:ℝ)≤(b:ℝ) by rw [←hleft,←hW];exact W.ordered)
  let N:=fun G ω=>MixedJointNamedIto.scalarNoise
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ W.observations b hgap hbH v G ω
  have hIto:=MixedJointNamedIto.finite_ito
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ W.observations b hgap hbH hJ v hvb
  have hIto':PhysicalIto.FiniteItoInput μ Y (StandardFiniteIto.rowCovariance 𝓕 μ H R) W.left W.right N:=by
    rw [hleft,hW]
    exact hIto
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨A,hA⟩:=hF.fderiv.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.fderiv.norm_bound
  obtain ⟨K,hK,hHK⟩:=hF.hessian_lipschitz
  have hB0:0≤B:=(norm_nonneg _).trans (hB 0)
  have hr:=backward_regular W (hF.smooth.of_le (by simp)) hM hA hB hB0 hK hHK
  filter_upwards [hIto' _ _ hr] with ω hω
  rw [PhysicalIto.backward_terminal W F,
    PhysicalIto.backward_eq_semigroup W F ⟨le_rfl,W.ordered⟩] at hω
  have htime:Y ω W.right=Y ω (b:ℝ):=congrArg (Y ω) hW
  rw [htime] at hω
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact cancellation W F _ t _

end SHE.MixedNamedBackwardStep
