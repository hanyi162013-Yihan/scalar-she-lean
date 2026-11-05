module
public import SHE.MovingPhysicalGammaCap
public import SHE.StandardItoParameterFubini
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.MovingPhysicalGammaVersion
open Set MeasureTheory FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance movingPhysicalGammaVersion_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingPhysicalGammaVersion_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingPhysicalGammaVersion_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingPhysicalGammaVersion_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingPhysicalGammaVersion_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingPhysicalGammaVersion_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingPhysicalGammaVersion_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingPhysicalGammaVersion_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (past terminal:ℝ→ℝ≥0)(hpast:Measurable past)(hterminal:Measurable terminal)
variable (hbH:∀r,terminal r≤H)(hH:(H:ℝ)≤1)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)(hU:0≤U)
variable (g:Fin 6→MovingPhysicalGammaKernel.Domain Ω→ℂ)
variable (hgm:∀i,@Measurable (MovingPhysicalGammaKernel.Domain Ω) ℂ
  (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (g i))
variable (B:ℝ)(hB:0≤B)(hg:∀i z,‖g i z‖≤B)
variable (c0 c1 r0 r1:ℝ×(ℝ≥0×Ω)→EllipticField m U)
variable (hc0:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ c0)
variable (hc1:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ c1)
variable (hr0:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ r0)
variable (hr1:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ r1)
variable (d:ℝ×(ℝ≥0×Ω)→ℝ)
variable (hd:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ d)
variable (hdb:∀z,0≤d z∧d z≤1)
local notation "Raw"=>MovingPhysicalGammaKernel.raw past terminal hκ hm g c0 c1 r0 r1 d

theorem section_measurable {E:Type*}[MeasurableSpace E]
    {f:ℝ×(ℝ≥0×Ω)→E}
    (hf:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ f)(r:ℝ):
    Measurable[𝓕.predictable] (fun p=>f (r,p)):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact hf.comp (measurable_const.prodMk measurable_id)
include hgm in
theorem fields_section (r:ℝ)(i:Fin 6):
    @Measurable ((ℝ≥0×Ω)×HeatCircle) ℂ (𝓕.predictable.prod inferInstance) _
      (fun z=>g i ((r,z.1),z.2)):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact (hgm i).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

def process (z:ℝ×HeatCircle):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  NativeJointPhysicalGammaInput.process 𝓕 (past z.1) (terminal z.1) hκ hm μ H (hbH z.1)
    ((NNReal.coe_le_coe.mpr (hbH z.1)).trans hH) B hB
    (fun i p=>g i ((z.1,p.1),p.2)) (fields_section 𝓕 g hgm z.1)
    (fun i p x=>hg i ((z.1,p),x))
    (fun p=>c0 (z.1,p)) (fun p=>c1 (z.1,p)) (fun p=>r0 (z.1,p)) (fun p=>r1 (z.1,p))
    (section_measurable 𝓕 hc0 z.1) (section_measurable 𝓕 hc1 z.1)
    (section_measurable 𝓕 hr0 z.1) (section_measurable 𝓕 hr1 z.1)
    (fun p=>d (z.1,p)) (section_measurable 𝓕 hd z.1) (fun p=>hdb (z.1,p)) z.2
local notation "Input"=>process 𝓕 μ H past terminal hbH hH hκ hm g hgm B hB hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb

include hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hH in
theorem process_ae (z:ℝ×HeatCircle):
    Input z=ᵐ[energyMeasure μ H] (fun p=>Raw ((z.1,p),z.2)):=
  NativeJointPhysicalGammaInput.process_ae 𝓕 (past z.1) (terminal z.1) hκ hm μ H (hbH z.1)
    ((NNReal.coe_le_coe.mpr (hbH z.1)).trans hH) B hB
    (fun i p=>g i ((z.1,p.1),p.2)) (fields_section 𝓕 g hgm z.1)
    (fun i p x=>hg i ((z.1,p),x))
    (fun p=>c0 (z.1,p)) (fun p=>c1 (z.1,p)) (fun p=>r0 (z.1,p)) (fun p=>r1 (z.1,p))
    (section_measurable 𝓕 hc0 z.1) (section_measurable 𝓕 hc1 z.1)
    (section_measurable 𝓕 hr0 z.1) (section_measurable 𝓕 hr1 z.1)
    (fun p=>d (z.1,p)) (section_measurable 𝓕 hd z.1) (fun p=>hdb (z.1,p)) z.2

include hpast hterminal hU hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hH in
/-- A genuine moving-past/native-root joint version of the ORIGINAL J
Gamma integral. Joint predictability and finite original parameter
energy are proved from the literal kernel; its exact energy is derived
from the SAME J isometry. -/
theorem exists_version (ν:Measure ℝ)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J):
    ∃Y:(ℝ×HeatCircle)×Ω→ℝ,Measurable Y ∧
      (∀ᵐz∂ν.prod AddCircle.haarAddCircle,(fun ω=>Y (z,ω))=ᵐ[μ] J.integral (Input z)) ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)=
        (∫⁻z,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((z.1,(t,ω)),z.2)‖^2) ∂μ ∂timeMeasure H
          ∂ν.prod AddCircle.haarAddCircle) ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)≤
        ENNReal.ofReal (MovingPhysicalGammaCap.constant B κ U H)*ν Set.univ ∧
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)<∞:=by
  have hraw:StronglyMeasurable[((inferInstance:MeasurableSpace (ℝ×HeatCircle)).prod 𝓕.predictable)]
      (fun z:(ℝ×HeatCircle)×(ℝ≥0×Ω)=>Raw ((z.1.1,z.2),z.1.2)):=by
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    exact (MovingPhysicalGammaKernel.raw_predictable 𝓕 past terminal hpast hterminal hκ hm g hgm
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd).comp_measurable
        ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hbound:(∫⁻z:ℝ×HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((z.1,(t,ω)),z.2)‖^2)
      ∂μ ∂timeMeasure H ∂ν.prod AddCircle.haarAddCircle)≤
      ENNReal.ofReal (MovingPhysicalGammaCap.constant B κ U H)*ν Set.univ:=by
    calc
      _≤∫⁻_:ℝ×HeatCircle,ENNReal.ofReal (MovingPhysicalGammaCap.constant B κ U H)
          ∂ν.prod AddCircle.haarAddCircle:=lintegral_mono (fun z=>
        MovingPhysicalGammaCap.energy_bound past terminal hκ hm hU g B hB hg c0 c1 r0 r1 d hdb μ H hbH hH z.1 z.2)
      _=_:=by
        simp only [lintegral_const]
        rw [←univ_prod_univ,Measure.prod_prod,
          show (AddCircle.haarAddCircle:Measure HeatCircle) Set.univ=1 from measure_univ,mul_one]
  have hfinite:=lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ))
  obtain ⟨Y,hY,hYa,hYe⟩:=StandardItoParameterFubini.energy J hF
    (ν.prod AddCircle.haarAddCircle) Input
    (fun z:(ℝ×HeatCircle)×(ℝ≥0×Ω)=>Raw ((z.1.1,z.2),z.1.2)) hraw
    (process_ae 𝓕 μ H past terminal hbH hH hκ hm g hgm B hB hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb) hfinite
  exact ⟨Y,hY,hYa,hYe,hYe.trans_le hbound,hYe.trans_lt hfinite⟩
end SHE.MovingPhysicalGammaVersion
