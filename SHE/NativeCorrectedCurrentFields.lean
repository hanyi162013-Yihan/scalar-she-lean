module

public import SHE.NativeHeatFunctionalEnergy
public import SHE.PredictablePastParameter

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.NativeCorrectedCurrentFields
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeCorrectedCurrentFields_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeCorrectedCurrentFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCorrectedCurrentFields_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCorrectedCurrentFields_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCorrectedCurrentFields_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCorrectedCurrentFields_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
variable (U V : ℝ≥0×Ω→RealL2) (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
variable (Λ θ : ℝ) (v b : ℝ≥0)

def pastD (ω : Ω) : RealL2:=V (v,ω)-U (v,ω)

include hU hV in
theorem pastD_measurable : Measurable[𝓕 v] (pastD U V v) :=
  (((show IsStronglyPredictable 𝓕 (Function.curry V) from hV).stronglyAdapted v).sub
    ((show IsStronglyPredictable 𝓕 (Function.curry U) from hU).stronglyAdapted v)).measurable

def state (p : ℝ≥0×Ω) : RealL2:=
  heat ((b:ℝ)-(p.1:ℝ)) (U p)+θ • (
    heat ((b:ℝ)-(p.1:ℝ)) (V p-U p)-
      (Real.exp (-Λ*((p.1:ℝ)-(v:ℝ)))*(1-Real.exp (-Λ*((b:ℝ)-(p.1:ℝ))))) •
        heat ((b:ℝ)-(v:ℝ)) (PredictablePastParameter.held v (pastD U V v) 0 p))

include hU hV in
/-- A genuine joint predictable L2 current field with the exact old
compensator. The clock in heat and in damping is the original native
physical clock. -/
theorem state_predictable : StronglyMeasurable[𝓕.predictable] (state U V Λ θ v b) := by
  have hcHeat : Continuous (fun p : ℝ×RealL2=>(p.1/timeScale,p.2)):=
    (continuous_fst.div_const timeScale).prodMk continuous_snd
  have hheat:=RealHeat.continuous_realHeat_action.comp hcHeat
  change Continuous (fun p : ℝ×RealL2=>heat p.1 p.2) at hheat
  have htime:=PredictableClock.real_time_measurable 𝓕
  have hh : StronglyMeasurable[𝓕.predictable]
      (PredictablePastParameter.held v (pastD U V v) 0):=
    (PredictablePastParameter.held_measurable 𝓕 v (pastD U V v) (pastD_measurable 𝓕 U V hU hV v) 0).stronglyMeasurable
  have htAge : Measurable[𝓕.predictable] (fun p : ℝ≥0×Ω=>(b:ℝ)-(p.1:ℝ)):=measurable_const.sub htime
  have h0:=hheat.comp_stronglyMeasurable (htAge.stronglyMeasurable.prodMk hU)
  have h1:=hheat.comp_stronglyMeasurable (htAge.stronglyMeasurable.prodMk (hV.sub hU))
  have hold:=(heat ((b:ℝ)-(v:ℝ))).continuous.comp_stronglyMeasurable hh
  have hc : StronglyMeasurable[𝓕.predictable]
      (fun p : ℝ≥0×Ω=>Real.exp (-Λ*((p.1:ℝ)-(v:ℝ)))*(1-Real.exp (-Λ*((b:ℝ)-(p.1:ℝ))))) := by
    exact (((htime.sub_const _).const_mul _).exp.mul
      (measurable_const.sub ((measurable_const.sub htime).const_mul _).exp)).stronglyMeasurable
  exact h0.add ((h1.sub (hc.smul hold)).const_smul θ)

include hU hV in
theorem scalar_predictable :
    @Measurable ((ℝ≥0×Ω)×HeatCircle) ℝ (𝓕.predictable.prod inferInstance) _
      (PredictableScalarField.nativeField (state U V Λ θ v b)) :=
  PredictableScalarField.nativeField_predictable 𝓕 (state_predictable 𝓕 U V hU hV Λ θ v b)

/-- Original current root displacement is literally the corrected
native Hilbert direction, pointwise on every covered current time. -/
theorem difference (q : ℝ≥0) (hvq : v<q) (ω : Ω) :
    state U V Λ 1 v b (q,ω)-state U V Λ 0 v b (q,ω)=
      NativeCurrentDifference.currentDifference Λ ((q:ℝ)-(v:ℝ)) ((b:ℝ)-(q:ℝ))
        (V (q,ω)-U (q,ω)) (pastD U V v ω) := by
  simp only [state,one_smul,zero_smul,add_zero,PredictablePastParameter.held_eq (p:=(q,ω)) _ _ hvq,
    NativeCurrentDifference.currentDifference]
  rw [show ((q:ℝ)-(v:ℝ))+((b:ℝ)-(q:ℝ))=(b:ℝ)-(v:ℝ) by ring]
  abel

/-- True scalar root energy, including the old correction, rather than
an assumed pointwise bound on the current random state. -/
theorem spatial_energy (hΛ : 0≤Λ) (q : ℝ≥0) (hvq : v<q) (hqb : q≤b) (ω : Ω) :
    (∫ x : HeatCircle,(PredictableScalarField.nativeField (state U V Λ 1 v b) ((q,ω),x)-
      PredictableScalarField.nativeField (state U V Λ 0 v b) ((q,ω),x))^2 ∂AddCircle.haarAddCircle)≤
      2*‖V (q,ω)-U (q,ω)‖^2+2*‖pastD U V v ω‖^2 := by
  rw [NativeRepresentativeEnergy.section_energy (state U V Λ 0 v b) (state U V Λ 1 v b) (q,ω),
    difference U V Λ v b q hvq ω]
  have hn:=pow_le_pow_left₀ (norm_nonneg _) (NativeCurrentDifference.currentDifference_norm hΛ
    (sub_nonneg.mpr (by exact_mod_cast hvq.le)) (sub_nonneg.mpr (by exact_mod_cast hqb))
    (V (q,ω)-U (q,ω)) (pastD U V v ω)) 2
  calc
    _≤(‖V (q,ω)-U (q,ω)‖+‖pastD U V v ω‖)^2:=hn
    _=2*‖V (q,ω)-U (q,ω)‖^2+2*‖pastD U V v ω‖^2-
        (‖V (q,ω)-U (q,ω)‖-‖pastD U V v ω‖)^2:=by ring
    _≤_:=sub_le_self _ (sq_nonneg _)

end SHE.NativeCorrectedCurrentFields
