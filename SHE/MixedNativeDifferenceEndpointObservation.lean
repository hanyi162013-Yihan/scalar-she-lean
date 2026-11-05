module
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativePairObservation
public import SHE.FullHorizonEndpointPositive
public import SHE.FullHorizonEndpointStop
public import SHE.FullHorizonTargetContinuity
public import SHE.HeatObservationEndpointLimit
public import SHE.ObservationTargetContinuity
public import SHE.TwoChannelRowsContinuity

public import SHE.MixedNativePairConstruction
public import SHE.NativePairObservedFirst
public import SHE.NativePairObservedSecond
public import SHE.NativePairFirstResolvent
public import SHE.NativePairControlObservation
public import SHE.NativePairResolvent

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

set_option quotPrecheck false
namespace SHE.MixedNativeDifferenceEndpointObservation
open Filter Topology
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
open MeasureTheory Set Filter PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels StoppedItoInputs DyadicApproximation
open scoped NNReal ENNReal
local instance nativePairObservedFirst_realSigma : MeasurableSpace RealL2 := borel _
local instance nativePairObservedFirst_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativePairObservedFirst_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativePairObservedFirst_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePairObservedFirst_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePairObservedFirst_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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

variable (b:ℝ≥0)(hbH:b≤H)
local notation "m0"=>hell.le.trans ((hbU 0).1.trans (hbU 0).2)

variable (hΛ:0≤Λ)
def firstRow (x:HeatCircle)(ε:ℝ):Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient
    (show (b:ℝ)≤(b:ℝ)+max ε 0 by linarith [le_max_right ε 0]) x hbH

def secondRow (x:HeatCircle)(ε:ℝ):Process (E:=RealHaarInput) 𝓕 μ H:=
  FullHorizonEndpoint.process 𝓕 μ H b hell m0
    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient
    (show (b:ℝ)≤(b:ℝ)+max ε 0 by linarith [le_max_right ε 0]) x hbH

def rows (x:HeatCircle)(ε:ℝ):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b
    (firstRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hbH x ε)
    (secondRow 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hbH x ε)
local notation "R"=>rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S b hbH hΛ
local notation "D"=>(fun ω=>Real.exp (Λ*(b:ℝ)) • (S.second b ω-S.first b ω))

include hIJ₀ hIJ₁ in
/-- The rescaled original difference has an actual zero-age scalar
endpoint representation. The integrating factor remains explicit. -/
theorem observation (hb0:0<b):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      PredictableScalarField.nativeField D (ω,x)=
        functional (b:ℝ) x (v₀-u₀)+J.integral (R x 0) ω:=by
  have hd:Measurable (fun ω=>S.second b ω-S.first b ω):=
    ((S.second_predictable.sub S.first_predictable).mono
      (predictable_le_product 𝓕)).measurable.comp
        ((measurable_const (a:=b)).prodMk (measurable_id : Measurable (id:Ω→Ω)))
  have hm:Measurable D:=hd.const_smul (Real.exp (Λ*(b:ℝ)))
  suffices hh:∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      PredictableScalarField.nativeField D (ω,x)=
        functional ((b:ℝ)+max (0:ℝ) 0) x (v₀-u₀)+J.integral (R x 0) ω by
    simpa only [max_self,add_zero] using hh
  apply HeatObservationEndpointLimit.physical_endpoint 𝓕 μ H J D hm R
    (fun x ε=>functional ((b:ℝ)+max ε 0) x (v₀-u₀))
  · intro x
    have hi:=(HeatAgeContinuity.continuousAt_circleHeat_age (show 0<(b:ℝ) by exact_mod_cast hb0) x).inner
      (𝕜:=ℂ) (continuousAt_const : ContinuousAt (fun _:ℝ=>embed (v₀-u₀)) (b:ℝ))
    have hc:ContinuousAt (fun t:ℝ=>functional t x (v₀-u₀)) (b:ℝ):=
      Complex.continuous_re.continuousAt.comp hi
    have ha:ContinuousAt (fun ε:ℝ=>(b:ℝ)+max ε 0) 0:=by fun_prop
    exact hc.comp_of_eq ha (by simp)
  · intro ε hε hε0 x
    have ht:Tendsto (fun n=>(b:ℝ)+max (ε n) 0) Filter.atTop (𝓝 (b:ℝ)):=by
      simpa only [max_self,add_zero] using
        (tendsto_const_nhds (x:=(b:ℝ))).add (hε0.max (tendsto_const_nhds (x:=(0:ℝ))))
    have h0:=FullHorizonTargetContinuity.tendsto 𝓕 μ H b hell m0
      (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hbH
      (le_refl (b:ℝ)) _ (fun n=>by linarith [le_max_right (ε n) 0]) ht x
    have h1:=FullHorizonTargetContinuity.tendsto 𝓕 μ H b hell m0
      (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient hbH
      (le_refl (b:ℝ)) _ (fun n=>by linarith [le_max_right (ε n) 0]) ht x
    simpa only [rows,firstRow,secondRow,max_self,add_zero] using
      TwoChannelRowsContinuity.rescaled_difference 𝓕 μ H h0 h1 hΛ b
  · intro ε hε x
    have hT:(b:ℝ)<(b:ℝ)+ε:=by linarith
    let N:=MixedNativePairScaledMartingale.normalizedInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S hΛ b hT x
    have hh:=MixedNativePairScaledMartingale.integral_representation 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hΛ b hbH hT x b le_rfl
    have hstop:StoppedItoInputs.stop 𝓕 μ H b N=N:=by
      unfold N MixedNativePairScaledMartingale.normalizedInput MixedNativePairScaledMartingale.rowDifference
      rw [StoppedInputAlgebra.stop_weighted,StoppedDampingClock.stop_sub]
      rw [←FullHorizonEndpointPositive.eq_prefix 𝓕 μ H b hell m0
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient hT x hbH,
        ←FullHorizonEndpointPositive.eq_prefix 𝓕 μ H b hell m0
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient hT x hbH,
        FullHorizonEndpointStop.self,FullHorizonEndpointStop.self]
    have he:R x ε=NativeHybridInput.rightLift 𝓕 μ H (Real.exp (Λ*(b:ℝ)) • N):=by
      simp only [rows,firstRow,secondRow,max_eq_left hε.le]
      rw [FullHorizonEndpointPositive.eq_prefix,FullHorizonEndpointPositive.eq_prefix]
      rfl
    have hj:J.integral (R x ε)=Real.exp (Λ*(b:ℝ)) • (rightIntegral 𝓕 μ H J).integral N:=by
      rw [he,NativeHybridInput.rightLift,map_smul,map_smul]
      rfl
    rw [hstop] at hh
    filter_upwards [hh,Lp.coeFn_smul (Real.exp (Λ*(b:ℝ))) ((rightIntegral 𝓕 μ H J).integral N)] with ω hh hs
    rw [hj,hs]
    simp only [map_smul,Pi.smul_apply,smul_eq_mul]
    simpa only [add_sub_cancel_left,max_eq_left hε.le] using hh

end SHE.MixedNativeDifferenceEndpointObservation
