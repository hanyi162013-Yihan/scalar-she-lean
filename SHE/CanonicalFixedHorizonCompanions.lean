module
public import SHE.GivenNativeMildFixedHorizon
public import SHE.SmoothApproximation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.CanonicalFixedHorizonCompanions
open MeasureTheory PredictableTimeDilation PredictableL2 LowBands FiniteHaar
open SmoothApproximation ScalarData
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩

theorem additive_pos(D:ScalarData):0<(ScalarReduction.additiveAmplitude D.lower)^2:=
  pow_pos (div_pos D.lower_pos (by norm_num)) 2

variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(h:ℝ≥0)(hh:(h:ℝ)≤1)(hpos:0<h)(D:ScalarData)
local notation "κ"=>(ScalarReduction.additiveAmplitude D.lower)^2
local notation "κpos"=>additive_pos D
local notation "haU"=>D.residual_continuous.measurable
local notation "hV"=>(fun n=>(D.smooth_boundedSmooth n).smooth.continuous.measurable)
local notation "Fil"=>filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)
local notation "Hor"=>NativeClock.rate*h
variable(J₀ J₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2)
  (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ (NativeClock.rate*h))
variable(hnull:NullCompleteFiltration.ContainsNullSets
  (filtration 𝓕 (clock NativeClock.rate NativeClock.rate_pos)) μ)
variable(B₀ B₁:ℝ≥0)(hBDG₀:StandardTerminalBDG16 J₀ B₀)(hBDG₁:StandardTerminalBDG16 J₁ B₁)
variable(u₀ v₀:StateL2)
variable(S:NativeFirstMildData.Data 𝓕 μ h ((ScalarReduction.additiveAmplitude D.lower)^2)
  (additive_pos D) D.residual_continuous.measurable D.ell_pos D.residual_bounds J₀ J₁ u₀)

include hh hpos hnull hBDG₀ hBDG₁ in
/-- One prescribed interval and the original two Itô integrals support
ALL canonical smooth companions and ALL nonnegative damping values.
The rough first path is exactly preserved. There is no smoothing-index
restriction, damping-index relation, or Lipschitz-dependent time loss. -/
theorem exists_all:
    ∀Λ:ℝ,0≤Λ→∀n:ℕ,
      ∃T:MixedNativeAdditiveResidualPair.Solution Fil μ Hor Λ κ κpos haU (hV n)
        D.ell_pos D.residual_bounds (D.smooth_bounds n) J₀ J₁ u₀ v₀,
        T.first=S.value:=by
  intro Λ hΛ n
  obtain ⟨L,hL⟩:=D.smooth_lipschitz n
  have hLC:LipschitzWith L (fun z=>(D.smoothCoefficient n z:ℂ)):=by
    simpa only [one_mul,Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hL
  exact GivenNativeMildFixedHorizon.exists_companion 𝓕 μ h hh hΛ κ κpos haU (hV n)
    D.ell_pos D.residual_bounds (D.smooth_bounds n) J₀ J₁
    D.beta_pos D.holderConstant_nonneg D.holderConstant_nonneg
    D.residual_holder (D.smooth_holder n) hLC hpos hnull B₀ B₁ hBDG₀ hBDG₁ u₀ v₀ S

end SHE.CanonicalFixedHorizonCompanions
