module
public import SHE.StandardItoStoppedParameterFubini
public import SHE.ItoParameterFubiniChannels
public import SHE.RotatedItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.StandardItoStoppedParameterFubini
open MeasureTheory PredictableL2 PredictableItoRotation OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω A C:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup A][InnerProductSpace ℝ A][MeasurableSpace A][BorelSpace A]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

/-- The ordinary stopped parameter property is inherited by constant
isometric channels of the SAME original J, including their original
deterministic-stop identities and path continuity. -/
theorem comp_isometry (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoStoppedParameterFubini J)(φ:A→ₗᵢ[ℝ] C):
    StandardItoStoppedParameterFubini (PredictableItoRotation.integral 𝓕 μ H (fun _=>φ)
      (StandardItoParameterFubini.constant_isometry_measurable 𝓕 φ) J):=by
  intro hnull X _ ν _ K raw hraw hK hfinite
  let hφ:=StandardItoParameterFubini.constant_isometry_measurable 𝓕 φ
  let K':X→Process (E:=C) 𝓕 μ H:=fun x=>processIsometry 𝓕 μ H (fun _=>φ) hφ (K x)
  have hr:StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)]
      (fun z=>φ (raw z)):=φ.continuous.comp_stronglyMeasurable hraw
  have hk(x:X):K' x=ᵐ[energyMeasure μ H] (fun p=>φ (raw (x,p))):=by
    filter_upwards [processIsometry_ae 𝓕 μ H (fun _=>φ) hφ (K x),hK x] with p hp hr
    rw [hp,hr]
  have ht:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖φ (raw (x,(t,ω)))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞:=by
    simpa only [φ.norm_map] using hfinite
  obtain ⟨Y,hY,hYa,hYc⟩:=hF hnull X ν K' (fun z=>φ (raw z)) hr hk ht
  refine ⟨Y,hY,?_,hYc⟩
  filter_upwards [hYa] with x hx
  intro q
  change (fun ω=>Y (x,(q,ω)))=ᵐ[μ]
    J.integral (processIsometry 𝓕 μ H (fun _=>φ) hφ (StoppedItoInputs.stop 𝓕 μ H (q:ℝ) (K x)))
  simpa only [K',←RotatedItoAlgebra.map_stop] using hx q

variable [SecondCountableTopology A]
local instance itoStoppedParameterChannels_bothSigma : MeasurableSpace (Both A):=borel _
local instance itoStoppedParameterChannels_bothBorel : BorelSpace (Both A):=⟨rfl⟩
theorem left (J:StandardTerminalIto (C:=Both A) (E:=ℝ) 𝓕 μ H)(hF:StandardItoStoppedParameterFubini J):
    StandardItoStoppedParameterFubini (leftIntegral 𝓕 μ H J):=
  comp_isometry 𝓕 μ H J hF (OrthogonalItoChannels.left (C:=A))
theorem right (J:StandardTerminalIto (C:=Both A) (E:=ℝ) 𝓕 μ H)(hF:StandardItoStoppedParameterFubini J):
    StandardItoStoppedParameterFubini (rightIntegral 𝓕 μ H J):=
  comp_isometry 𝓕 μ H J hF (OrthogonalItoChannels.right (C:=A))
end SHE.StandardItoStoppedParameterFubini
