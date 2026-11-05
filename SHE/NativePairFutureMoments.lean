module

public import SHE.NativePairFutureMean
public import SHE.NativeHybridMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.NativePairFutureMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

def displacement (q : ℝ≥0) {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (θ : ℝ) (i : Fin n) (ω : Ω) : ℝ :=
  futureMeanVector Λ target centers q q.2 (embed u₀) (embed (v₀-u₀))
    (embed (S.first q ω)) (embed (S.second q ω-S.first q ω)) θ i-
    ControlledProfile.mean Λ (embed u₀) (embed (v₀-u₀)) (θ,(target i,nativeCenter centers i))

include hIJ₀ hIJ₁ in
/-- Actual compensated future means are centered at the printed
controlled profile, at every original target. Their all fixed fractional
moments follow from the genuine same-driver hybrid integral; current
states are not asserted to be Gaussian or independent of the profile. -/
theorem fractional_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {n : ℕ} (target : Fin n→ℝ) (centers : Fin n→UnitAddCircle)
    (hgap : ∀ i,(q:ℝ)<target i) {θ : ℝ} (hθ : |θ|≤1)
    (i : Fin n) (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ i ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ i ω|^(((2*p:ℕ):ℝ)*β) ∂μ) ≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  have hy := NativePairFutureMean.future_mean_displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH target centers hgap hθ
  have hh := NativeHybridMoments.fractional_moment 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q (hgap i) (nativeCenter centers i) hΛ hθ J hqH hq1 p B hBDG hβ hβ1
  have he : (fun ω => |displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q target centers θ i ω|^(((2*p:ℕ):ℝ)*β)) =ᵐ[μ]
      fun ω => |J.integral (NativePairHybridIdentity.input 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
        q (hgap i) (nativeCenter centers i) hΛ hθ) ω|^(((2*p:ℕ):ℝ)*β) := by
    filter_upwards [hy] with ω hω
    exact congrArg (fun z : ℝ => |z|^(((2*p:ℕ):ℝ)*β)) (hω i)
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans_le hh.2⟩

end SHE.NativePairFutureMoments
