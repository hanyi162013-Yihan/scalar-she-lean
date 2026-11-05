module

public import SHE.NativeControlledGaussianFields
public import SHE.LocalizedFiniteIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.NativeControlledGaussianIto
open MeasureTheory Set GaussianIncrement NativeHeatObservation NativeObservationNaturality
open SmoothCylinders FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open NativeControlledGaussianFields
open scoped NNReal ENNReal
local instance nativeControlledGaussianIto_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeControlledGaussianIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeControlledGaussianIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeControlledGaussianIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeControlledGaussianIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeControlledGaussianIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {n : ℕ}

def test (W : ClippedCovariance.ObservationWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (u₀ v₀ : RealL2) (t : ℝ) (z : State (n+n)) : ℝ :=
  GaussianConvolution.gaussianAverage (W.path t).val F
    (mean Λ θ u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center) t z)

def testDerivative (W : ClippedCovariance.ObservationWindow n) (F : State n→ℝ)
    (Λ θ : ℝ) (u₀ v₀ : RealL2) : ℝ→State (n+n)→ℝ :=
  GaussianAffineFields.derivative W F
    (DampedAffineGaussian.linear Λ θ (ObservationBlockMaps.first n) (ObservationBlockMaps.second n))
    (DampedAffineGaussian.linearDerivative Λ θ (ObservationBlockMaps.second n))
    (DampedAffineGaussian.shift Λ θ
      (initialDifference u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center))
      (terminalShift Λ θ u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center)))
    (DampedAffineGaussian.shiftDerivative Λ θ
      (initialDifference u₀ v₀ (fun i => (W.observations i).target) (fun i => (W.observations i).center)))

theorem smoothTimeTest (W : ClippedCovariance.ObservationWindow n) (hleft : 0≤W.left)
    {F : State n→ℝ} (hF : BoundedSmooth F) {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) (u₀ v₀ : RealL2) :
    LocalizedItoTest.SmoothTimeTest W.left W.right (test W F Λ θ u₀ v₀) (testDerivative W F Λ θ u₀ v₀) :=
  DampedAffineGaussian.smoothTimeTest W hleft hF hΛ θ _ _ _ _

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
/-- Genuine controlled Gaussian-reserve Itô identity for the actual
native additive/residual pair. The sole formula input is the original
universal finite-dimensional Itô package; all Gaussian test conditions,
continuous/predictable observation construction and row representation
are proved. The displayed covariance window is common and positive-gap. -/
theorem formula (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hΛ : 0≤Λ)
    (W : ClippedCovariance.ObservationWindow n) (hleft : 0≤W.left)
    (b : ℝ≥0) (hW : W.right=(b:ℝ)) (hbH : b≤H)
    {F : State n→ℝ} (hF : BoundedSmooth F) (θ : ℝ) :
    let target := fun i => (W.observations i).target
    let centers := fun i => (W.observations i).center
    let Y := Function.uncurry
      (NativePairExtendedMartingale.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b)
    ∃ N : Ω→ℝ,Integrable N μ ∧ (∫ ω,N ω ∂μ)=0 ∧
      ∀ᵐ ω ∂μ,test W F Λ θ u₀ v₀ b (Y (b,ω))=
        test W F Λ θ u₀ v₀ W.left (Y (W.left.toNNReal,ω))+N ω+
          ∫ t in W.left..(b:ℝ),testDerivative W F Λ θ u₀ v₀ t (Y (t.toNNReal,ω))+(1/2:ℝ)*
            GaussianTaylorAverage.covarianceAction
              (StandardFiniteIto.rowCovariance 𝓕 μ H
                (NativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b
                  (fun i => by have hh := W.target_gap i; rw [hW] at hh; linarith [W.gap_pos]) hΛ) ω t)
              (GaussianTaylor.hessian (test W F Λ θ u₀ v₀ t) (Y (t.toNNReal,ω))) := by
  intro target centers Y
  have hgap : ∀ i,(b:ℝ)<target i := by
    intro i
    have hh := W.target_gap i
    rw [hW] at hh
    exact lt_of_lt_of_le (by linarith [W.gap_pos] : (b:ℝ)<(b:ℝ)+W.gap) (by linarith)
  let R := NativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b hgap hΛ
  have hY : StronglyMeasurable[𝓕.predictable] Y := NativePairExtendedMartingale.predictable_value
    𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ target centers b hgap hnull hΛ hbH
  let N := FiniteItoNoise.noise 𝓕 μ H Y hY R J W.left b (test W F Λ θ u₀ v₀)
  refine ⟨N,FiniteItoNoise.noise_integrable 𝓕 μ H Y hY R J W.left b _,
    FiniteItoNoise.noise_centered 𝓕 μ H Y hY R J W.left b _,?_⟩
  have htest : LocalizedItoTest.SmoothTimeTest W.left (b:ℝ)
      (test W F Λ θ u₀ v₀) (testDerivative W F Λ θ u₀ v₀) := by
    rw [← hW]
    exact smoothTimeTest W hleft hF hΛ θ u₀ v₀
  have hh := LocalizedFiniteIto.formula 𝓕 μ H J hJ R
    (NativePairExtendedMartingale.initial u₀ v₀ target centers) Y hY
    (NativePairExtendedMartingale.continuous_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b)
    (fun t _ => NativePairExtendedMartingale.integral_representation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      J hIJ₀ hIJ₁ target centers b hgap hΛ hbH t) hleft (by simpa only [hW] using W.ordered)
    (by exact_mod_cast hbH) (test W F Λ θ u₀ v₀) (testDerivative W F Λ θ u₀ v₀) htest
  simpa only [Real.toNNReal_coe] using hh

end SHE.NativeControlledGaussianIto
