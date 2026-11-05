module
public import SHE.MovingCanonicalFrozenRows
public import SHE.MixedNativeGammaEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MovingNativeGammaCoefficients
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open DyadicApproximation MovingCanonicalFrozenRows
open scoped NNReal ENNReal
local instance movingNativeGammaCoefficients_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingNativeGammaCoefficients_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingNativeGammaCoefficients_realSigma : MeasurableSpace RealL2:=borel _
local instance movingNativeGammaCoefficients_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingNativeGammaCoefficients_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingNativeGammaCoefficients_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativeGammaCoefficients_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingNativeGammaCoefficients_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(hκP:κ<P.lower)(W:ℝ)
local notation "Lower"=>MixedNativeGammaEnergy.commonLower (ell:=ell) (P:=P) (κ:=κ)
local notation "Bound"=>MixedNativeGammaEnergy.commonUpper (M:=M) (P:=P) (κ:=κ)

def first (z:ℝ×(ℝ≥0×Ω)):EllipticField Lower Bound:=
  MixedNativeGammaEnergy.currentFirst 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P z.2
def second (z:ℝ×(ℝ≥0×Ω)):EllipticField Lower Bound:=
  MixedNativeGammaEnergy.currentSecond 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P z.2
theorem first_predictable:
    @Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _
      (first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P):=
  (MixedNativeGammaEnergy.currentFirst_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P).comp measurable_snd
theorem second_predictable:
    @Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _
      (second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P):=
  (MixedNativeGammaEnergy.currentSecond_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P).comp measurable_snd

def frozen (θ:ℝ)(z:ℝ×(ℝ≥0×Ω)):EllipticField Lower Bound:=
  NativeCanonicalGammaEnergy.widen P κ (min_le_right _ _) (le_max_right _ _)
    (MovingCanonicalFrozenRows.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W
      ((z.1,(z.2.1,0)),z.2))

theorem frozen_predictable (θ:ℝ):
    @Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _
      (frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W θ):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have ht:=PredictableClock.time_measurable 𝓕
  have hp:Measurable (fun z:ℝ×(ℝ≥0×Ω)=>((z.1,(z.2.1,(0:HeatCircle))),z.2)):=
    (measurable_fst.prodMk ((ht.comp measurable_snd).prodMk measurable_const)).prodMk measurable_snd
  have hf:=MovingCanonicalFrozenRows.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W
  exact (NativeCanonicalGammaEnergy.widen_measurable P κ (min_le_right _ _) (le_max_right _ _)).comp
    (hf.comp_measurable hp).measurable

/-- These are exactly the original common-cast frozen factors; the
moving realization does not change the Haar coupling or its fields. -/
theorem frozen_section (θ r:ℝ)(p:ℝ≥0×Ω):
    frozen 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP W θ (r,p)=
      NativeCanonicalGammaEnergy.frozen (v:=NativeMovingGammaClock.past W r)
        (U:=Function.uncurry S.first) (V:=Function.uncurry S.second) (P:=P) (Λ:=Λ) (κ:=κ)
        (hκP:=hκP) (hmP:=min_le_right _ _) (hWP:=le_max_right _ _) θ p:=rfl
end SHE.MovingNativeGammaCoefficients
