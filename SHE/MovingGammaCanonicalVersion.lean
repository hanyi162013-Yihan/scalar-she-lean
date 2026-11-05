module
public import SHE.MovingPhysicalGammaVersion
public import SHE.NativeGammaInputCongruence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.MovingGammaCanonicalVersion
open Set MeasureTheory FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance movingGammaCanonicalVersion_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingGammaCanonicalVersion_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingGammaCanonicalVersion_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingGammaCanonicalVersion_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingGammaCanonicalVersion_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingGammaCanonicalVersion_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingGammaCanonicalVersion_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingGammaCanonicalVersion_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (past terminal:ℝ→ℝ≥0)(hpast:Measurable past)(hterminal:Measurable terminal)
variable (hbH:∀r,terminal r≤H)(hH:(H:ℝ)≤1)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)(hU:0≤U)
variable (g:Fin 6→MovingPhysicalGammaKernel.Domain Ω→ℂ)
variable (hgm:∀i,@Measurable (MovingPhysicalGammaKernel.Domain Ω) ℂ
  (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (g i))
variable (B:ℝ)(hB:0≤B)(hg:∀i z,‖g i z‖≤B)
variable (f:ℝ→Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hfm:∀r i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (f r i))
variable (hf:∀r i p x,‖f r i (p,x)‖≤B)
variable (c0 c1 r0 r1:ℝ×(ℝ≥0×Ω)→EllipticField m U)
variable (hc0:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ c0)
variable (hc1:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ c1)
variable (hr0:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ r0)
variable (hr1:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ r1)
variable (d:ℝ×(ℝ≥0×Ω)→ℝ)
variable (hd:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ d)
variable (hdb:∀z,0≤d z∧d z≤1)
local notation "Input"=>MovingPhysicalGammaVersion.process 𝓕 μ H past terminal hbH hH hκ hm
  g hgm B hB hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb

/-- The fixed-past canonical input is the original predictable L²
process, with unchanged coefficients and the SAME stopped window. -/
def canonicalProcess (r:ℝ)(x:HeatCircle):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  NativeJointPhysicalGammaInput.process 𝓕 (past r) (terminal r) hκ hm μ H (hbH r)
    ((NNReal.coe_le_coe.mpr (hbH r)).trans hH) B hB (f r) (hfm r) (hf r)
    (fun p=>c0 (r,p)) (fun p=>c1 (r,p)) (fun p=>r0 (r,p)) (fun p=>r1 (r,p))
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hc0 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hc1 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hr0 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hr1 r)
    (fun p=>d (r,p)) (MovingPhysicalGammaVersion.section_measurable 𝓕 hd r) (fun p=>hdb (r,p)) x
local notation "Canonical"=>canonicalProcess 𝓕 μ H past terminal hbH hH hκ hm B hB f hfm hf
  c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb

include hgm hg hfm hf hc0 hc1 hr0 hr1 hd hdb hbH hH in
theorem process_eq (r:ℝ)(x:HeatCircle)
    (he:∀ᵐp∂energyMeasure μ H,p∈NativeGammaClock.window (past r) (terminal r)→∀i,
      g i ((r,p),x)=f r i (p,x)):
    Input (r,x)=Canonical r x:=by
  exact NativeGammaInputCongruence.process_eq (past r) (terminal r) hκ hm
    (fun i z=>g i ((r,z.1),z.2)) (f r)
    (fun p=>c0 (r,p)) (fun p=>c1 (r,p)) (fun p=>r0 (r,p)) (fun p=>r1 (r,p))
    (fun p=>d (r,p)) 𝓕 μ H (hbH r) ((NNReal.coe_le_coe.mpr (hbH r)).trans hH) B hB
    (MovingPhysicalGammaVersion.fields_section 𝓕 g hgm r) (hfm r)
    (fun i p x=>hg i ((r,p),x)) (hf r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hc0 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hc1 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hr0 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hr1 r)
    (MovingPhysicalGammaVersion.section_measurable 𝓕 hd r) (fun p=>hdb (r,p)) x he

include hpast hterminal hU hgm hg hfm hf hc0 hc1 hr0 hr1 hd hdb hbH hH in
/-- The actual moving joint version has exactly the original canonical
SAME-J section. No jointly measurable choice of the pre-existing
fixed-past versions is assumed. -/
theorem exists_version (ν:Measure ℝ)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J)
    (he:∀ᵐr∂ν,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
      ∀ᵐp∂energyMeasure μ H,p∈NativeGammaClock.window (past r) (terminal r)→∀i,
        g i ((r,p),x)=f r i (p,x)):
    ∃Y:(ℝ×HeatCircle)×Ω→ℝ,Measurable Y ∧
      (∀ᵐr∂ν,∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,
        (fun ω=>Y ((r,x),ω))=ᵐ[μ] J.integral (Canonical r x)) ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)≤
        ENNReal.ofReal (MovingPhysicalGammaCap.constant B κ U H)*ν Set.univ ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)<∞:=by
  obtain ⟨Y,hY,hYa,hYe,hYb,hYf⟩:=MovingPhysicalGammaVersion.exists_version
    𝓕 μ H past terminal hpast hterminal hbH hH hκ hm hU g hgm B hB hg
    c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb ν J hF
  refine ⟨Y,hY,?_,hYb,hYf⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hYa,he] with r hr he
  filter_upwards [hr,he] with x hx he
  rw [process_eq 𝓕 μ H past terminal hbH hH hκ hm g hgm B hB hg f hfm hf
    c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb r x he] at hx
  exact hx
end SHE.MovingGammaCanonicalVersion
