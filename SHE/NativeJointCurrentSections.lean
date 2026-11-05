module
public import SHE.NativeJointGammaCurrent
public import SHE.NativeObservableFields
public import SHE.NativeCorrectedCurrentFields
public import SHE.NativeCurrentRootIdentity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeJointCurrentSections
open Set MeasureTheory PredictableL2 NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeJointCurrentSections_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeJointCurrentSections_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointCurrentSections_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeJointCurrentSections_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeJointCurrentSections_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointCurrentSections_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointCurrentSections_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeJointCurrentSections_realSecond : SecondCountableTopology RealL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]
attribute [local irreducible] functional NativeJointGammaCurrent.state

/-- Actual native joint current and physical heat observations agree
on the full root/time/sample product, with a positive-age implication. -/
theorem product_ae (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (ν:Measure (ℝ≥0×Ω)) [SFinite ν]
    (U V:ℝ≥0×Ω→RealL2) (hU:StronglyMeasurable[𝓕.predictable] U)
    (hV:StronglyMeasurable[𝓕.predictable] V) (Λ θ:ℝ) (b:ℝ≥0):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐp∂ν,p.1<b→
      PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ θ b) (p,x)=
        functional ((b:ℝ)-(p.1:ℝ)) x (U p)+
          θ*Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))*functional ((b:ℝ)-(p.1:ℝ)) x (V p-U p):=by
  have hu:Measurable U:=(hU.mono (predictable_le_product 𝓕)).measurable
  have hv:Measurable V:=(hV.mono (predictable_le_product 𝓕)).measurable
  have hn:Measurable (PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ θ b)):=
    PredictableScalarField.nativeField_measurable
      ((NativeJointGammaCurrent.state_predictable 𝓕 U V hU hV Λ θ b).mono
        (predictable_le_product 𝓕)).measurable
  have ht:Measurable (fun z:(ℝ≥0×Ω)×HeatCircle=>(b:ℝ)-(z.1.1:ℝ)):=
    measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)
  have hf0:=observable_measurable (hu.comp measurable_fst) ht measurable_snd
  have hf1:=observable_measurable ((hv.sub hu).comp measurable_fst) ht measurable_snd
  have he:MeasurableSet {z:(ℝ≥0×Ω)×HeatCircle|¬z.1.1<b ∨
      PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ θ b) z=
        functional ((b:ℝ)-(z.1.1:ℝ)) z.2 (U z.1)+
          θ*Real.exp (-Λ*((b:ℝ)-(z.1.1:ℝ)))*functional ((b:ℝ)-(z.1.1:ℝ)) z.2 (V z.1-U z.1)}:=
    ((measurableSet_lt measurable_fst.fst measurable_const).compl).union
      (measurableSet_eq_fun hn (hf0.add (((ht.const_mul (-Λ)).exp.const_mul θ).mul hf1)))
  have hs:∀ᵐp∂ν,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,¬p.1<b ∨
      PredictableScalarField.nativeField (NativeJointGammaCurrent.state U V Λ θ b) (p,x)=
        functional ((b:ℝ)-(p.1:ℝ)) x (U p)+
          θ*Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))*functional ((b:ℝ)-(p.1:ℝ)) x (V p-U p):=by
    apply ae_of_all
    intro p
    by_cases hp:p.1<b
    · exact (NativeJointGammaCurrent.scalar_ae U V Λ θ b p.1 hp p.2).mono (fun x hx=>Or.inr hx)
    · exact ae_of_all _ (fun _=>Or.inl hp)
  have hswap:=(Measure.ae_ae_comm he).1 hs
  filter_upwards [hswap] with x hx
  filter_upwards [hx] with p hp hpb
  exact hp.resolve_left (not_not_intro hpb)

end SHE.NativeJointCurrentSections
