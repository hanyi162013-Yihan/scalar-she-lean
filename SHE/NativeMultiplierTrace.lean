module

public import SHE.HaarUnifiedNegative
public import SHE.NativeSignedHaarProcess
public import SHE.NativeKernelAction
public import SHE.NativeHeatConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeMultiplierTrace
open Set MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel FiniteHaar
open scoped ENNReal
local instance nativeMultiplierTrace_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance nativeMultiplierTrace_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

def multiplier (b : CircleL2) (B : ℝ) (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B) : CircleL2→L[ℂ]CircleL2 :=
  CircleNormalization.push.toLinearIsometry.toContinuousLinearMap.comp
    ((CircleMultiplier.operator (CircleNormalization.push.symm b) B
      (CircleNormalization.push_symm_ae_property b (fun z => ‖z‖≤B) hb)).comp
      CircleNormalization.push.symm.toLinearIsometry.toContinuousLinearMap)

theorem multiplier_ae (b : CircleL2) (B : ℝ) (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B) (v : CircleL2) :
    (multiplier b B hb v : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x => b x*v x := by
  let c := CircleNormalization.push.symm b
  let u := CircleNormalization.push.symm v
  let hc := CircleNormalization.push_symm_ae_property b (fun z => ‖z‖≤B) hb
  have hm := (CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae
    (CircleMultiplier.operator_ae c B hc u)
  have hb' := CircleNormalization.push_ae c
  have hv' := CircleNormalization.push_ae u
  rw [CircleNormalization.push.apply_symm_apply] at hb' hv'
  filter_upwards [CircleNormalization.push_ae (CircleMultiplier.operator c B hc u),hm,hb',hv']
    with x hx hm hb' hv'
  change multiplier b B hb v x=b x*v x
  change CircleNormalization.push (CircleMultiplier.operator c B hc u) x=_
  rw [hx,hm,←hb',←hv']

/-- Literal native Fourier heat equals convolution with the physical
period-2π kernel on every L2 input. -/
theorem native_heat_convolution_ae {t : ℝ} (ht : 0<t) (v : CircleL2) :
    (circleHeatOperator t ht.le v : HeatCircle→ℂ)=ᵐ[haarAddCircle]
      fun x => ∫ y : HeatCircle,ProfileVariance.heatPhysical t x y*v y ∂haarAddCircle := by
  filter_upwards [heat_kernel_inner_ae ht v] with x hx
  rw [←hx,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ProfileVariance.heatPhysical_ae ht x] with y hy
  rw [←hy,RCLike.inner_apply,←WordRecursion.heatPhysical_real ht x y,Complex.conj_ofReal]
  ring

theorem integralOperator_eq_multiplier_heat {X : Type*} [MeasurableSpace X]
    {F : X×(HeatCircle×HeatCircle)→ℂ} (hF : Measurable F) {C : ℝ} (hC : 0≤C)
    (hFC : ∀ z y x,‖F (z,(y,x))‖≤C) {t : ℝ} (ht : 0<t)
    (bfield : X×HeatCircle→ℂ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B) (z : X)
    (hba : (b : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x => bfield (z,x))
    (hactual : ∀ y x,F (z,(y,x))=bfield (z,x)*ProfileVariance.heatPhysical t x y)
    (v : CircleL2) : integralOperator F z v=multiplier b B hb (circleHeatOperator t ht.le v) := by
  apply Lp.ext
  filter_upwards [integralOperator_ae hF hC hFC z v,multiplier_ae b B hb (circleHeatOperator t ht.le v),
    native_heat_convolution_ae ht v,hba] with x hx hm hh hb'
  rw [hx,hm,hh,hb',←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by dsimp only;rw [hactual];ring)

theorem multiplier_heat_push (b : CircleL2) (B : ℝ) (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B)
    {t : ℝ} (ht : 0≤t) (v : CircleHeat.CircleL2) :
    multiplier b B hb (circleHeatOperator t ht (CircleNormalization.push v))=
      CircleNormalization.push (CircleMultiplier.operator (CircleNormalization.push.symm b) B
        (CircleNormalization.push_symm_ae_property b (fun z => ‖z‖≤B) hb)
        (CircleHeat.heat (NativeHeatSpan.clock t) v)) := by
  have he : (2*π)^2*NativeHeatSpan.clock t=t := by unfold NativeHeatSpan.clock;field_simp;ring
  have hh : CircleNormalization.push (CircleHeat.heat (NativeHeatSpan.clock t) v)=
      circleHeatOperator t ht (CircleNormalization.push v) := by
    simpa only [he] using CircleNormalization.push_heat (NativeHeatSpan.clock t) (div_nonneg ht (by positivity)) v
  rw [←hh]
  change CircleNormalization.push (CircleMultiplier.operator (CircleNormalization.push.symm b) B
    (CircleNormalization.push_symm_ae_property b (fun z => ‖z‖≤B) hb)
    (CircleNormalization.push.symm (CircleNormalization.push (CircleHeat.heat (NativeHeatSpan.clock t) v))))=_
  rw [CircleNormalization.push.symm_apply_apply]

/-- The same signed Haar pair with an arbitrary bounded native output
multiplier has the integrable age^-1/2 trace, including the leading term. -/
theorem exists_signed_multiplier_trace (m U : ℝ) (hm : 0<m) {ρ : ℝ}
    (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ (mass t : ℝ) (hmass : 1≤mass) (ht : 0<t),t≤1 →
      ∀ (b : CircleL2) (B : ℝ) (hB : 0≤B) (hb : ∀ᵐ x ∂haarAddCircle,‖b x‖≤B)
        (c d : EllipticField m U),
      Summable (fun i : HaarNode => ‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (multiplier b B hb (circleHeatOperator t ht.le
          (CircleNormalization.push (globalHaarColumn i d.1-globalHaarColumn i c.1))))‖^2) ∧
      (∑' i : HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (multiplier b B hb (circleHeatOperator t ht.le
          (CircleNormalization.push (globalHaarColumn i d.1-globalHaarColumn i c.1))))‖^2)≤
        C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hmass hρ.le c d := by
  obtain ⟨C,hC,htrace⟩ := exists_global_signed_negative_trace m U hm hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro mass t hmass ht ht1 b B hB hb c d
  have hct : 0<NativeHeatSpan.clock t := NativeHeatSpan.clock_pos ht
  have hct1 : NativeHeatSpan.clock t≤1 := by
    apply (div_le_one (by positivity : (0:ℝ)<4*π^2)).mpr
    exact ht1.trans (by nlinarith [Real.two_le_pi])
  let hb' := CircleNormalization.push_symm_ae_property b (fun z => ‖z‖≤B) hb
  have hh := htrace mass (NativeHeatSpan.clock t) hmass hct hct1
    (NativeSignedHaarProcess.realCoefficient c) (NativeSignedHaarProcess.realCoefficient d)
    (by simpa only [NativeSignedHaarProcess.realEmbed_realCoefficient] using c.2.2)
    (by simpa only [NativeSignedHaarProcess.realEmbed_realCoefficient] using d.2.2)
    (CircleNormalization.push.symm b) B hB hb'
  have he (i : HaarNode) : ‖OneInputOperator.besselHalf mass ρ hmass hρ.le
      (multiplier b B hb (circleHeatOperator t ht.le
        (CircleNormalization.push (globalHaarColumn i d.1-globalHaarColumn i c.1))))‖^2=
      ‖HaarWeightedHeat.weightedHeat mass ρ (NativeHeatSpan.clock t) hmass hρ.le
        (CircleNormalization.push.symm b) B hb' (globalHaarColumn i d.1-globalHaarColumn i c.1)‖^2 := by
    rw [multiplier_heat_push b B hb ht.le]
    change _=‖CircleNormalization.push.symm (OneInputOperator.besselHalf mass ρ hmass hρ.le
      (CircleNormalization.push _))‖^2
    rw [CircleNormalization.push.symm.norm_map]
    rfl
  have hinput : StepInput.negativeEnergy 1 mass ρ
      (DyadicApproximation.realEmbed (NativeSignedHaarProcess.realCoefficient d-NativeSignedHaarProcess.realCoefficient c))=
      NativeSignedHaarProcess.inputEnergy hmass hρ.le c d := by
    rw [map_sub,NativeSignedHaarProcess.realEmbed_realCoefficient,NativeSignedHaarProcess.realEmbed_realCoefficient,
      NativeSignedHaarProcess.inputEnergy,CircleNormalization.push_bessel_energy]
  simpa only [he,NativeSignedHaarProcess.realEmbed_realCoefficient,hinput] using hh

end SHE.NativeMultiplierTrace
