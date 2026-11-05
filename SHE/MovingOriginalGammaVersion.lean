module
public import SHE.MovingCanonicalGammaSections
public import SHE.MovingGammaCanonicalVersion
public import SHE.MovingNativeGammaCoefficients
public import SHE.MovingGammaClockFields
public import SHE.JointGammaNativeInput
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.MovingOriginalGammaVersion
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation SmoothCylinders
open scoped NNReal ENNReal
local instance movingOriginalGammaVersion_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingOriginalGammaVersion_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingOriginalGammaVersion_realSigma : MeasurableSpace RealL2:=borel _
local instance movingOriginalGammaVersion_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingOriginalGammaVersion_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingOriginalGammaVersion_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingOriginalGammaVersion_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingOriginalGammaVersion_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingOriginalGammaVersion_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingOriginalGammaVersion_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingOriginalGammaVersion_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingOriginalGammaVersion_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(hκP:κ<P.lower)(W h:ℝ)
variable (hW:0≤W)(hh:0<h)(hcover:W+h≤H)(hH:(H:ℝ)≤1)(hΛ:0≤Λ)
local notation "Past"=>NativeMovingGammaClock.past W
local notation "Terminal"=>NativeMovingGammaClock.terminal W h
local notation "covered" r:max=>NativeMovingGammaClock.terminal_le hW hh.le H hcover r
local notation "one" r:max=>(show (Terminal r:ℝ)≤1 from
  (show (Terminal r:ℝ)≤(H:ℝ) by exact_mod_cast covered r).trans hH)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Bound"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)
local notation "LowerPos"=>MixedNativeGammaEnergy.commonLower_pos (ell:=ell) (P:=P) (κ:=κ) (hell:=hell) (hκP:=hκP)
local notation "Canon"=>MovingNativeGammaFields.canonical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH
local notation "C0"=>MovingNativeGammaCoefficients.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "C1"=>MovingNativeGammaCoefficients.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "R" θ:max=>MovingNativeGammaCoefficients.frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W θ
local notation "C0m"=>MovingNativeGammaCoefficients.first_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "C1m"=>MovingNativeGammaCoefficients.second_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P
local notation "Rm" θ:max=>MovingNativeGammaCoefficients.frozen_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W θ
local notation "Damping"=>MovingGammaClockFields.damping Past Terminal Λ
local notation "Dm"=>MovingGammaClockFields.damping_predictable 𝓕 Past Terminal
  (NativeMovingGammaClock.past_measurable W) (NativeMovingGammaClock.terminal_measurable W h) Λ
local notation "Db"=>MovingGammaClockFields.damping_bounds Past Terminal hΛ
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)
variable {a:ℝ→ℝ}(ha:BoundedSmooth a){A:ℝ}(hA:0≤A)
variable (hholder:∀z w,|a z-a w|≤A*|z-w|^P.exponent)(j:ℕ)
local notation "Cap"=>ScalarHeatSingleMultiplier.cap A P.exponent j
local notation "CanonM"=>MovingCanonicalGammaSections.canonical_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
  I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH hnull B0 B1 hBDG0 hBDG1 ha j
local notation "CanonB"=>fun r=>NativeJointGammaFields.fields_bound
  (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=Past r) (b:=Terminal r) (hbH:=covered r) (hb1:=one r)
  (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
  (hU:=S.first_predictable) (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ)
  (hκ:=hκ) (hκP:=hκP) (I0:=I₀) (I1:=I₁) ha hA P.exponent_pos.le P.exponent_le_one hholder j
local notation "CapNonneg"=>JointGammaNativeInput.cap_nonneg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁
  u₀ v₀ S P hκP (Past 0) (Terminal 0) (covered 0) hH ha j hA P.exponent_pos.le P.exponent_le_one hholder

/-- Literal original finite-Itô/native physical input at the actual
moving window, with full-target frozen rows and convex damping. -/
def input (r:ℝ)(x:HeatCircle):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  JointGammaNativeInput.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP hΛ
    (Past r) (Terminal r) (covered r) hH ha j (NativeMovingGammaClock.terminal_pos hW hh r)
    hnull B0 B1 hBDG0 hBDG1 hA P.exponent_pos.le P.exponent_le_one hholder x
local notation "Input"=>input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH hΛ
  hnull B0 B1 hBDG0 hBDG1 ha hA hholder j

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hF:StandardItoStoppedParameterFubini J)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hF hIJ0 hIJ1 in
/-- The moving original finite-Itô Gamma inputs admit ONE jointly Borel
scalar output driven by the SAME original J. All moving profile,
predictable-input, stopping and canonical-section identities are proved. -/
theorem exists_version (ν:Measure ℝ)[IsFiniteMeasure ν]:
    ∃Y:(ℝ×HeatCircle)×Ω→ℝ,Measurable Y ∧
      (∀ᵐr∂ν,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
        (fun ω=>Y ((r,x),ω))=ᵐ[μ] J.integral (Input r x)) ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)≤
        ENNReal.ofReal (MovingPhysicalGammaCap.constant Cap κ Bound H)*ν Set.univ ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)<∞:=by
  obtain ⟨g,hg,hgb,hgr,hge⟩:=MovingCanonicalGammaSections.exists_sections
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W h hW hh hcover hH
    hnull B0 B1 hBDG0 hBDG1 ha hA hholder j J hF hIJ0 hIJ1 ν
  have hUpper:0≤Bound:=(hell.le.trans ((hbU 0).1.trans (hbU 0).2)).trans (le_max_left _ _)
  obtain ⟨Y,hY,hYa,hYb,hYf⟩:=MovingGammaCanonicalVersion.exists_version
    𝓕 μ H Past Terminal (NativeMovingGammaClock.past_measurable W)
    (NativeMovingGammaClock.terminal_measurable W h) (fun r=>covered r) hH hκ LowerPos hUpper
    g hg Cap CapNonneg hgb (Canon a j) CanonM CanonB C0 C1 (R 0) (R 1)
    C0m C1m (Rm 0) (Rm 1) Damping Dm Db ν J
    (StandardItoStoppedParameterFubini.ambient J hF hnull) hge
  refine ⟨Y,hY,?_,hYb,hYf⟩
  filter_upwards [hYa] with r hr
  filter_upwards [hr] with x hx
  convert hx using 1
  rfl
end SHE.MovingOriginalGammaVersion
