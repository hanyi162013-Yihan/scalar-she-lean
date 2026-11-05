module

public import SHE.NativeJointIto
public import SHE.NativeControlledGenerator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeJointBackwardStep
open MeasureTheory Set NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open GaussianItoTest GaussianTaylor GaussianTaylorAverage CovarianceEndpoint
open scoped NNReal ENNReal
local instance nativeJointBackwardStep_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointBackwardStep_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointBackwardStep_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointBackwardStep_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointBackwardStep_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointBackwardStep_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

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
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- Actual drift-free joint backward step before the original stops.
Its only stochastic formula assumption is the original universal Itô
package. Singular Gaussian covariance and colliding observations are
allowed; the reference PDE and its cancellation are proved. -/
theorem one_step (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    {n : ℕ} (W : EndpointWindow n) (hleft : 0≤W.left)
    (b : ℝ≥0) (hW : W.right=(b:ℝ)) (hbH : b≤H)
    (hgap : ∀ i,(b:ℝ)<(W.observations i).target)
    (_hstop : ∀ i,(b:ℝ)≤(W.observations i).stop)
    {F : State n→ℝ} (hF : BoundedSmooth F) :
    let Y := fun (ω : Ω) (t : ℝ) => NativeJointObservations.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      W.observations b t.toNNReal ω
    let R := NativeJointObservations.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S W.observations b hgap hΛ
    ∃ N : Ω→ℝ,Integrable N μ ∧ (∫ ω,N ω ∂μ)=0 ∧ ∀ᵐ ω ∂μ,
      F (Y ω b)=WordRecursion.gaussianSemigroup W.coefficient W.observations W.left W.right F (Y ω W.left)+N ω+
        ∫ t in W.left..W.right,(1/2:ℝ)*covarianceAction
          (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
          (hessian (backward W F t) (Y ω t)) := by
  intro Y R
  obtain ⟨N,hNc,hIto⟩ := NativeJointIto.finiteItoInput 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hnull hJ hΛ W.observations b hgap hbH hleft (by simpa only [hW] using W.ordered)
  have hIto' : PhysicalIto.FiniteItoInput μ Y (StandardFiniteIto.rowCovariance 𝓕 μ H R)
      W.left W.right N := by rw [hW];exact hIto
  obtain ⟨M,hM⟩ := hF.norm_bound
  obtain ⟨A,hA⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  obtain ⟨K,hK,hHK⟩ := hF.hessian_lipschitz
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0)
  have hr := backward_regular W (hF.smooth.of_le (by simp)) hM hA hB hB0 hK hHK
  refine ⟨N (backward W F),(hNc _).1,(hNc _).2,?_⟩
  filter_upwards [hIto' _ _ hr] with ω hω
  rw [PhysicalIto.backward_terminal W F,
    PhysicalIto.backward_eq_semigroup W F ⟨le_rfl,W.ordered⟩] at hω
  have htime : Y ω W.right=Y ω (b:ℝ) := congrArg (Y ω) hW
  rw [htime] at hω
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact cancellation W F _ t _

end SHE.NativeJointBackwardStep
