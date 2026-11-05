module
public import SHE.MovingCanonicalPredictableReference
public import SHE.MovingCanonicalVariance
public import SHE.MovingJointCurrent
public import SHE.NativeJointGammaFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.MovingNativeGammaFields
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation SmoothCylinders
open scoped NNReal ENNReal
local instance movingNativeGammaFields_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingNativeGammaFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingNativeGammaFields_realSigma : MeasurableSpace RealL2:=borel _
local instance movingNativeGammaFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingNativeGammaFields_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingNativeGammaFields_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingNativeGammaFields_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingNativeGammaFields_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingNativeGammaFields_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingNativeGammaFields_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
abbrev Domain (Ω:Type*):=((ℝ×(ℝ≥0×Ω))×HeatCircle)
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(hκP:κ<P.lower)(W h:ℝ)
variable (hW:0≤W)(hh:0<h)(hcover:W+h≤H)(hH:(H:ℝ)≤1)
local notation "past" r:max=>NativeMovingGammaClock.past W r
local notation "terminal" r:max=>NativeMovingGammaClock.terminal W h r
local notation "covered" r:max=>NativeMovingGammaClock.terminal_le hW hh.le H hcover r
local notation "one" r:max=>(show (terminal r:ℝ)≤1 from
  (show (terminal r:ℝ)≤(H:ℝ) by exact_mod_cast covered r).trans hH)

def canonical (a:ℝ→ℝ)(j:ℕ)(r:ℝ):Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ:=
  NativeJointGammaFields.fields (𝓕:=𝓕) (μ:=μ) (H:=H) (v:=past r) (b:=terminal r)
    (hbH:=covered r) (hb1:=one r) (U:=Function.uncurry S.first) (V:=Function.uncurry S.second)
    (hU:=S.first_predictable) (hV:=S.second_predictable) (P:=P) (Λ:=Λ) (κ:=κ) (hκ:=hκ) (hκP:=hκP)
    (I0:=I₀) (I1:=I₁) a j

local notation "Var" θ:max=>MovingCanonicalVariance.variance 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W P θ h
local notation "Cur" θ:max=>PredictableScalarField.nativeField
  (MovingJointCurrent.state (Function.uncurry S.first) (Function.uncurry S.second) Λ θ W h)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hF:StandardItoStoppedParameterFubini J)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I₀ B0)(hBDG1:StandardTerminalBDG16 I₁ B1)
variable {a:ℝ→ℝ}(ha:BoundedSmooth a){A:ℝ}(hA:0≤A)
variable (hholder:∀z w,|a z-a w|≤A*|z-w|^P.exponent)(j:ℕ)

include hW hh hcover hH hF hIJ0 hIJ1 hnull hBDG0 hBDG1 ha hA hholder in
/-- All SIX actual native joint-Gamma heat-band multipliers admit a
genuine moving-past/predictable/root realization with the original
uniform band cap. The simultaneous canonical-field equality holds on
the ORIGINAL past/time/root/sample product. -/
theorem exists_fields (ν:Measure ℝ)[IsFiniteMeasure ν]:
    ∃g:Fin 6→Domain Ω→ℂ,
      (∀i,@Measurable (Domain Ω) ℂ
        (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (g i)) ∧
      (∀i z,‖g i z‖≤ScalarHeatSingleMultiplier.cap A P.exponent j) ∧
      ∀ᵐr∂ν,∀ᵐq∂timeMeasure H,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
        past r<q→q≤terminal r→∀i,
          g i ((r,(q,ω)),x)=canonical 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hκP
            W h hW hh hcover hH a j r i ((q,ω),x):=by
  have href(θ:ℝ):=MovingCanonicalPredictableReference.exists_version 𝓕 μ H Λ κ hκ
    haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W h hW hh hcover hH J hF
    hIJ0 hIJ1 hnull B0 B1 hBDG0 hBDG1 ν
  obtain ⟨R0,hR0,hR0a⟩:=href 0
  obtain ⟨R1,hR1,hR1a⟩:=href 1
  let g:Fin 6→Domain Ω→ℂ:=ScalarHeatSixFields.fields a j (Var 0) (Var 1) (Cur 0) (Cur 1) R0 R1
  have hvar(θ:ℝ):@Measurable (Domain Ω) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (Var θ):=
    MovingCanonicalVariance.variance_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W P θ h
  have hcur(θ:ℝ):@Measurable (Domain Ω) ℝ
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (Cur θ):=
    MovingJointCurrent.scalar_predictable 𝓕 (Function.uncurry S.first) (Function.uncurry S.second)
      S.first_predictable S.second_predictable Λ θ W h
  refine ⟨g,?_,?_,?_⟩
  · letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    exact ScalarHeatSixFields.measurable ha j (hvar 0) (hvar 1) (hcur 0) (hcur 1) hR0 hR1
  · intro i z
    exact ScalarHeatSixFields.bound ha hA P.exponent_pos.le P.exponent_le_one hholder j
      (Var 0) (Var 1) (Cur 0) (Cur 1) R0 R1 i z.1 z.2
  · filter_upwards [hR0a,hR1a] with r hr0 hr1
    filter_upwards [hr0,hr1] with q hr0 hr1
    filter_upwards [hr0,hr1] with x hr0 hr1
    filter_upwards [hr0,hr1] with ω hr0 hr1
    intro hvq hqb i
    have hv0:=MovingCanonicalVariance.variance_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W P 0 h hW hh.le r q hvq hqb ω x
    have hv1:=MovingCanonicalVariance.variance_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S W P 1 h hW hh.le r q hvq hqb ω x
    unfold g canonical NativeJointGammaFields.fields
    fin_cases i <;>
      simp only [ScalarHeatSixFields.fields,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_zero',Matrix.cons_val_succ',
        ScalarHeatSingleMultiplier.field,hv0,hv1,hr0 hvq hqb,hr1 hvq hqb] <;> rfl
end SHE.MovingNativeGammaFields
