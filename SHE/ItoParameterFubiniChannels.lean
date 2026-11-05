module
public import SHE.StandardItoParameterFubini
public import SHE.OrthogonalItoChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.StandardItoParameterFubini
open MeasureTheory PredictableL2 PredictableItoRotation OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω A C:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup A][InnerProductSpace ℝ A][MeasurableSpace A][BorelSpace A]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

def constant_isometry_measurable (φ:A→ₗᵢ[ℝ] C):
    @Measurable ((ℝ≥0×Ω)×A) C (𝓕.predictable.prod inferInstance) _
      (fun p=>φ p.2):=φ.continuous.measurable.comp measurable_snd

/-- The ordinary parameterized-Fubini property is inherited by every
constant isometric input channel of the SAME original integral. -/
theorem comp_isometry (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J)(φ:A→ₗᵢ[ℝ] C):
    StandardItoParameterFubini (PredictableItoRotation.integral 𝓕 μ H (fun _=>φ)
      (constant_isometry_measurable 𝓕 φ) J):=by
  intro X _ ν _ K raw hraw hK hfinite
  let K':X→Process (E:=C) 𝓕 μ H:=fun x=>processIsometry 𝓕 μ H (fun _=>φ)
    (constant_isometry_measurable 𝓕 φ) (K x)
  have hr:StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)]
      (fun z=>φ (raw z)):=φ.continuous.comp_stronglyMeasurable hraw
  have hk(x:X):K' x=ᵐ[energyMeasure μ H] (fun p=>φ (raw (x,p))):=by
    filter_upwards [processIsometry_ae 𝓕 μ H (fun _=>φ) (constant_isometry_measurable 𝓕 φ) (K x),hK x]
      with p hp hr
    rw [hp,hr]
  have ht:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖φ (raw (x,(t,ω)))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞:=by
    simpa only [φ.norm_map] using hfinite
  obtain ⟨Y,hY,hYa⟩:=hF X ν K' (fun z=>φ (raw z)) hr hk ht
  exact ⟨Y,hY,hYa⟩

variable [SecondCountableTopology A]
local instance itoParameterFubiniChannels_bothSigma : MeasurableSpace (Both A):=borel _
local instance itoParameterFubiniChannels_bothBorel : BorelSpace (Both A):=⟨rfl⟩

theorem left (J:StandardTerminalIto (C:=Both A) (E:=ℝ) 𝓕 μ H)(hF:StandardItoParameterFubini J):
    StandardItoParameterFubini (leftIntegral 𝓕 μ H J):=
  comp_isometry 𝓕 μ H J hF (OrthogonalItoChannels.left (C:=A))

theorem right (J:StandardTerminalIto (C:=Both A) (E:=ℝ) 𝓕 μ H)(hF:StandardItoParameterFubini J):
    StandardItoParameterFubini (rightIntegral 𝓕 μ H J):=
  comp_isometry 𝓕 μ H J hF (OrthogonalItoChannels.right (C:=A))
end SHE.StandardItoParameterFubini
