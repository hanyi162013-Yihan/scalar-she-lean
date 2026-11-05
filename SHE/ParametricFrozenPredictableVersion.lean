module
public import SHE.ParametricStoppedHaarEnergy
public import SHE.StandardItoStoppedParameterFubini
public import SHE.FrozenRowStopping
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ParametricFrozenPredictableVersion
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier ParametricStoppedHaarRows
open scoped NNReal ENNReal
local instance parametricFrozenPredictableVersion_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance parametricFrozenPredictableVersion_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance parametricFrozenPredictableVersion_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω:Type*}{X:Type}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable (v b:X→ℝ≥0)(center:X→HeatCircle)(f:X×(ℝ≥0×Ω)→EllipticField ell M)
variable (hf:StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)] f)
variable (hv:Measurable v)(hb:Measurable b)(hc:Measurable center)
variable (hbH:∀x,b x≤H)(hH:(H:ℝ)≤1)
local notation "Raw"=>ParametricStoppedHaarRows.raw hell v b b center f
local notation "Input"=>ParametricStoppedHaarRows.process 𝓕 μ H hell hM v b b center f hf (fun _=>le_rfl) hbH

include hv hb hc hH in
/-- All analytic applicability for the ordinary stopped parameter input
is derived for actual moving full-target native Haar rows. Its output
is genuinely parameter/predictable, and its partial-stop identification
uses the SAME original J for every stop on one parameter-AE event. -/
theorem exists_version (ν:Measure X)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoStoppedParameterFubini J)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ):
    ∃Y:X×(ℝ≥0×Ω)→ℝ,
      StronglyMeasurable[((inferInstance:MeasurableSpace X).prod 𝓕.predictable)] Y ∧
      (∀ᵐx∂ν,∀q:ℝ≥0,∀hq:q≤b x,
        (fun ω=>Y (x,(q,ω)))=ᵐ[μ] J.integral
          (NativeFrozenSpatialObservation.row 𝓕 μ H (b x) q (v x) hell hM
            (fun p=>f (x,p)) (field_section 𝓕 f hf x) (hbH x) hq (center x) 0)) ∧
      (∀ᵐx∂ν,∀ᵐω∂μ,Continuous (fun q=>Y (x,(q,ω)))):=by
  have hbound:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)≤
      ENNReal.ofReal (ParametricStoppedHaarEnergy.constant M H)*ν Set.univ:=by
    calc
      _≤∫⁻_:X,ENNReal.ofReal (ParametricStoppedHaarEnergy.constant M H) ∂ν:=
        lintegral_mono (ParametricStoppedHaarEnergy.energy_bound 𝓕 μ H hell hM v b b center f
          (fun _=>le_rfl) hbH hH)
      _=_:=by simp
  have hfinite:(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞:=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ))
  obtain ⟨Y,hY,hYa,hYc⟩:=hF hnull X ν Input Raw
    (raw_predictable 𝓕 hell v b b center f hf hv hb hb hc)
    (process_ae 𝓕 μ H hell hM v b b center f hf (fun _=>le_rfl) hbH) hfinite
  refine ⟨Y,hY,?_,hYc⟩
  filter_upwards [hYa] with x hx
  intro q hq
  have he:=FrozenRowStopping.stop_row 𝓕 μ H (b x) q (v x) hell hM
    (fun p=>f (x,p)) (field_section 𝓕 f hf x) (hbH x) hq (center x)
  simpa only [ParametricStoppedHaarRows.process,he] using hx q
end SHE.ParametricFrozenPredictableVersion
