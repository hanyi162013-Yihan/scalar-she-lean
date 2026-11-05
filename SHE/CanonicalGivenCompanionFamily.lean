module
public import SHE.CanonicalFixedHorizonCompanions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.CanonicalGivenCompanionFamily
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar
open SmoothApproximation ScalarData
open scoped NNReal ENNReal
local instance :Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance :MeasurableSpace StateL2:=borel _
local instance :BorelSpace StateL2:=⟨rfl⟩
local instance :MeasurableSpace CircleHeat.CircleL2:=borel _
local instance :BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance :MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance :BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {ι:Type}(Ω:ι→Type)[∀i,MeasurableSpace (Ω i)]
variable (𝓕:∀i,Filtration ℝ≥0 (inferInstance:MeasurableSpace (Ω i)))
  (μ:∀i,Measure (Ω i))[∀i,IsProbabilityMeasure (μ i)]
variable (h:ℝ≥0)(hh:(h:ℝ)≤1)(hpos:0<h)(D:ScalarData)
local notation "κ"=>(ScalarReduction.additiveAmplitude D.lower)^2
local notation "κpos"=>CanonicalFixedHorizonCompanions.additive_pos D
local notation "Fil" i:max=>filtration (𝓕 i) (clock NativeClock.rate NativeClock.rate_pos)
local notation "Hor"=>NativeClock.rate*h
variable (J₀ J₁:∀i,StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2)
  (filtration (𝓕 i) (clock NativeClock.rate NativeClock.rate_pos)) (μ i) (NativeClock.rate*h))
variable (hnull:∀i,NullCompleteFiltration.ContainsNullSets
  (filtration (𝓕 i) (clock NativeClock.rate NativeClock.rate_pos)) (μ i))
variable (B₀ B₁:ι→ℝ≥0)(hBDG₀:∀i,StandardTerminalBDG16 (J₀ i) (B₀ i))
  (hBDG₁:∀i,StandardTerminalBDG16 (J₁ i) (B₁ i))
variable (u₀:ι→StateL2)
variable (U:∀i,NativeFirstMildData.Data (𝓕 i) (μ i) h ((ScalarReduction.additiveAmplitude D.lower)^2)
  (CanonicalFixedHorizonCompanions.additive_pos D) D.residual_continuous.measurable D.ell_pos
  D.residual_bounds (J₀ i) (J₁ i) (u₀ i))
include hh hpos hnull hBDG₀ hBDG₁ in
/-- Given rough native solutions on different original spaces acquire
ALL canonical companions on their original two drivers. Their rough
first paths are preserved exactly, simultaneously in k and n. -/
theorem exists_family(Λ:ℕ→ℝ)(hΛ:∀k,0≤Λ k):
    ∃S:∀i k n,MixedNativeAdditiveResidualPair.Solution (Fil i) (μ i) Hor (Λ k) κ κpos
      D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
      D.ell_pos D.residual_bounds (D.smooth_bounds n) (J₀ i) (J₁ i) (u₀ i) (u₀ i),
      ∀i k n,(S i k n).first=(U i).value:=by
  classical
  have he(i:ι)(k n:ℕ):∃S:MixedNativeAdditiveResidualPair.Solution (Fil i) (μ i) Hor (Λ k) κ κpos
      D.residual_continuous.measurable ((D.smooth_boundedSmooth n).smooth.continuous.measurable)
      D.ell_pos D.residual_bounds (D.smooth_bounds n) (J₀ i) (J₁ i) (u₀ i) (u₀ i),
      S.first=(U i).value:=
    CanonicalFixedHorizonCompanions.exists_all (𝓕 i) (μ i) h hh hpos D (J₀ i) (J₁ i)
      (hnull i) (B₀ i) (B₁ i) (hBDG₀ i) (hBDG₁ i) (u₀ i) (u₀ i) (U i) (Λ k) (hΛ k) n
  choose S hS using he
  exact ⟨S,hS⟩
end SHE.CanonicalGivenCompanionFamily
