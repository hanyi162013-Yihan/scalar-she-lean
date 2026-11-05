module
public import SHE.NativeCorrectedCurrentFields
public import SHE.NativeCurrentRootIdentity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeJointGammaCurrent
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeJointGammaCurrent_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeJointGammaCurrent_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointGammaCurrent_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeJointGammaCurrent_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeJointGammaCurrent_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointGammaCurrent_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointGammaCurrent_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeJointGammaCurrent_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]

/-- Literal native joint backward current. Its damping is the
remaining target age; there is no old-state compensation in this state. -/
def state (U V:ℝ≥0×Ω→RealL2) (Λ θ:ℝ) (b:ℝ≥0) (p:ℝ≥0×Ω):RealL2:=
  heat ((b:ℝ)-(p.1:ℝ)) (U p)+
    θ • (Real.exp (-Λ*((b:ℝ)-(p.1:ℝ))) • heat ((b:ℝ)-(p.1:ℝ)) (V p-U p))

theorem state_predictable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (U V:ℝ≥0×Ω→RealL2) (hU:StronglyMeasurable[𝓕.predictable] U)
    (hV:StronglyMeasurable[𝓕.predictable] V) (Λ θ:ℝ) (b:ℝ≥0):
    StronglyMeasurable[𝓕.predictable] (state U V Λ θ b):=by
  have hcHeat:Continuous (fun p:ℝ×RealL2=>(p.1/timeScale,p.2)):=
    (continuous_fst.div_const timeScale).prodMk continuous_snd
  have hheat:=RealHeat.continuous_realHeat_action.comp hcHeat
  change Continuous (fun p:ℝ×RealL2=>heat p.1 p.2) at hheat
  have htime:=PredictableClock.real_time_measurable 𝓕
  have hage:Measurable[𝓕.predictable] (fun p:ℝ≥0×Ω=>(b:ℝ)-(p.1:ℝ)):=measurable_const.sub htime
  have h0:=hheat.comp_stronglyMeasurable (hage.stronglyMeasurable.prodMk hU)
  have h1:=hheat.comp_stronglyMeasurable (hage.stronglyMeasurable.prodMk (hV.sub hU))
  have he:StronglyMeasurable[𝓕.predictable] (fun p:ℝ≥0×Ω=>Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))):=
    ((hage.const_mul (-Λ)).exp).stronglyMeasurable
  exact h0.add ((he.smul h1).const_smul θ)

theorem scalar_predictable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (U V:ℝ≥0×Ω→RealL2) (hU:StronglyMeasurable[𝓕.predictable] U)
    (hV:StronglyMeasurable[𝓕.predictable] V) (Λ θ:ℝ) (b:ℝ≥0):
    @Measurable _ ℝ (𝓕.predictable.prod inferInstance) _
      (PredictableScalarField.nativeField (state U V Λ θ b)):=
  PredictableScalarField.nativeField_predictable 𝓕 (state_predictable 𝓕 U V hU hV Λ θ b)

@[simp] theorem state_zero (U V:ℝ≥0×Ω→RealL2) (Λ:ℝ) (b:ℝ≥0) (p:ℝ≥0×Ω):
    state U V Λ 0 b p=heat ((b:ℝ)-(p.1:ℝ)) (U p):=by simp only [state,zero_smul,add_zero]

theorem difference (U V:ℝ≥0×Ω→RealL2) (Λ:ℝ) (b:ℝ≥0) (p:ℝ≥0×Ω):
    state U V Λ 1 b p-state U V Λ 0 b p=
      Real.exp (-Λ*((b:ℝ)-(p.1:ℝ))) • heat ((b:ℝ)-(p.1:ℝ)) (V p-U p):=by
  simp only [state,one_smul,zero_smul,add_zero,add_sub_cancel_left]

/-- Exact native scalar representative of the ORIGINAL joint current
at every positive heat age. This is the Hilbert/finite-observation
coherence required for the literal joint martingale. -/
theorem scalar_ae (U V:ℝ≥0×Ω→RealL2) (Λ θ:ℝ) (b q:ℝ≥0) (hqb:q<b) (ω:Ω):
    (fun x=>PredictableScalarField.nativeField (state U V Λ θ b) ((q,ω),x))=ᵐ[AddCircle.haarAddCircle]
      (fun x=>functional ((b:ℝ)-(q:ℝ)) x (U (q,ω))+
        θ*Real.exp (-Λ*((b:ℝ)-(q:ℝ)))*functional ((b:ℝ)-(q:ℝ)) x (V (q,ω)-U (q,ω))):=by
  let τ:ℝ:=(b:ℝ)-(q:ℝ)
  let c:ℝ:=θ*Real.exp (-Λ*τ)
  have ht:0<τ:=sub_pos.mpr (by exact_mod_cast hqb)
  have hs:state U V Λ θ b (q,ω)=heat τ (U (q,ω)+c • (V (q,ω)-U (q,ω))):=by
    simp only [state,τ,c,map_add,map_smul,smul_smul]
  have he:=NativeHeatFunctionalEnergy.functional_ae ht (U (q,ω)+c • (V (q,ω)-U (q,ω)))
  refine he.symm.mono (fun x hx=>?_)
  change PredictableScalarField.nativeField (fun _:Unit=>state U V Λ θ b (q,ω)) ((),x)=_
  change PredictableScalarField.nativeField (fun _:Unit=>heat τ (U (q,ω)+c • (V (q,ω)-U (q,ω)))) ((),x)=
    functional τ x (U (q,ω)+c • (V (q,ω)-U (q,ω))) at hx
  rw [hs,hx]
  simp only [map_add,map_smul,smul_eq_mul,c,τ]
end SHE.NativeJointGammaCurrent
