module

public import SHE.NativePairHybridIdentity
public import SHE.NativeHybridMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.NativePairHybridMoments
open Set MeasureTheory ProbabilityTheory Real PredictableL2 NativeHeatObservation
  NativeObservationNaturality FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
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

def displacement (q : ℝ≥0) (T : ℝ) (x : HeatCircle) (θ : ℝ) (ω : Ω) : ℝ :=
  functional (T-(q:ℝ)) x (S.first q ω+θ • (S.second q ω-S.first q ω))-
    (functional T x u₀+θ*Real.exp (-Λ*(q:ℝ))*functional T x (v₀-u₀))

include hIJ₀ hIJ₁ in
/-- The actual constructed two-channel native pair has the same bounded
all-even current displacement moments as its genuine full-horizon input.
The deterministic damping is at the current time q, with original further
heat target T retained. -/
theorem moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hθ : |θ|≤1)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B) :
    (∫⁻ ω,ENNReal.ofReal
      (‖displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q T x θ ω‖^(2*p)) ∂μ) ≤
      ENNReal.ofReal (NativeHybridMoments.momentConstant p B κ M*(q:ℝ)^((p:ℝ)/2)) := by
  have hy := NativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hT x hθ
  have hh := NativeHybridMoments.moment 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ J hqH hq1 p B hBDG
  rw [show (∫⁻ ω,ENNReal.ofReal
      (‖displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q T x θ ω‖^(2*p)) ∂μ) =
      ∫⁻ ω,ENNReal.ofReal (‖J.integral
        (NativePairHybridIdentity.input 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x hΛ hθ) ω‖^(2*p)) ∂μ from
    lintegral_congr_ae (hy.fun_comp (fun z : ℝ => ENNReal.ofReal (‖z‖^(2*p))))]
  exact hh

include hIJ₀ hIJ₁ in
/-- Actual current-state fractional displacement, without Gaussianity
or independence assumptions on the state or the reference profile. -/
theorem fractional_moment (hΛ : 0≤Λ) (q : ℝ≥0) (hqH : q≤H) (hq1 : (q:ℝ)≤1)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) {θ : ℝ} (hθ : |θ|≤1)
    (p : ℕ) (B : ℝ≥0) (hBDG : StandardTerminalBDGPower p J B)
    {β : ℝ} (hβ : 0≤β) (hβ1 : β≤1) :
    Integrable (fun ω => |displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q T x θ ω|^(((2*p:ℕ):ℝ)*β)) μ ∧
      (∫ ω,|displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q T x θ ω|^(((2*p:ℕ):ℝ)*β) ∂μ) ≤
        (NativeHybridMoments.momentConstant p B κ M)^β*(q:ℝ)^((p:ℝ)*β/2) := by
  have hy := NativePairHybridIdentity.centered_current 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hΛ q hqH hT x hθ
  have hh := NativeHybridMoments.fractional_moment 𝓕 μ H hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (ContinuousHeatMild.coefficientFunction ha hell hb S.first)
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    S.first_coefficient S.second_coefficient q hT x hΛ hθ J hqH hq1 p B hBDG hβ hβ1
  have he : (fun ω => |displacement 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q T x θ ω|^(((2*p:ℕ):ℝ)*β)) =ᵐ[μ]
      fun ω => |J.integral (NativePairHybridIdentity.input 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q hT x hΛ hθ) ω|^(((2*p:ℕ):ℝ)*β) :=
    hy.fun_comp (fun z : ℝ => |z|^(((2*p:ℕ):ℝ)*β))
  exact ⟨hh.1.congr he.symm,(integral_congr_ae he).trans_le hh.2⟩

end SHE.NativePairHybridMoments
