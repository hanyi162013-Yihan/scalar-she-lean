module

public import SHE.NativePhysicalGammaVersion

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.NativeJointPhysicalGammaInput
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance nativeJointPhysicalGammaInput_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointPhysicalGammaInput_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeJointPhysicalGammaInput_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointPhysicalGammaInput_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointPhysicalGammaInput_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeJointPhysicalGammaInput_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance nativeJointPhysicalGammaInput_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance nativeJointPhysicalGammaInput_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v b:ℝ≥0)
variable {κ m U:ℝ} (hκ:0<κ) (hm:0<m)
variable (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1)
variable (B:ℝ) (hB:0≤B) (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
variable (hc0:Measurable[𝓕.predictable] c0) (hc1:Measurable[𝓕.predictable] c1)
variable (hr0:Measurable[𝓕.predictable] r0) (hr1:Measurable[𝓕.predictable] r1)
variable (d:ℝ≥0×Ω→ℝ) (hd:Measurable[𝓕.predictable] d) (hdb:∀p,0≤d p ∧ d p≤1)

/-- The main joint-current convex row. Its predictable weight is INSIDE
the original integral, and the frozen-reference gradients are retained. -/
def raw (z:(ℝ≥0×Ω)×HeatCircle):Both RealHaarInput:=
  d z.1 • NativePhysicalGammaKernel.raw v b hκ hm g c0 c1 r0 r1 z+
    (1-d z.1) • NativePhysicalGammaKernel.raw v b hκ hm g c0 c0 r0 r1 z
local notation "Raw"=>raw v b hκ hm g c0 c1 r0 r1 d

include hgm hc0 hc1 hr0 hr1 hd in
theorem raw_predictable : StronglyMeasurable[𝓕.predictable.prod inferInstance] Raw := by
  have h0:=NativePhysicalGammaKernel.raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1 hc0 hc1 hr0 hr1
  have h1:=NativePhysicalGammaKernel.raw_predictable 𝓕 v b hκ hm g hgm c0 c0 r0 r1 hc0 hc0 hr0 hr1
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact ((hd.comp measurable_fst).stronglyMeasurable.smul h0).add
    ((measurable_const.sub (hd.comp measurable_fst)).stronglyMeasurable.smul h1)

private theorem convex_norm_sq {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a:E) (b:E) {t:ℝ} (ht:0≤t) (ht1:t≤1) :
    ‖t • a+(1-t) • b‖^2≤t*‖a‖^2+(1-t)*‖b‖^2 := by
  have hn:=norm_add_le (t • a) ((1-t) • b)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr ht1)] at hn
  have hs:=pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he:=mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) (sq_nonneg (‖a‖-‖b‖))
  nlinarith

include hB hg hdb in
theorem raw_majorized (p:ℝ≥0×Ω) (x:HeatCircle):
    ‖Raw (p,x)‖^2≤NativePhysicalGammaInput.majorant v b (κ:=κ) (U:=U) B p := by
  have h0:=NativePhysicalGammaInput.raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 p x
  have h1:=NativePhysicalGammaInput.raw_majorized v b hκ hm B hB g hg c0 c0 r0 r1 p x
  have hj:=convex_norm_sq (NativePhysicalGammaKernel.raw v b hκ hm g c0 c1 r0 r1 (p,x))
    (NativePhysicalGammaKernel.raw v b hκ hm g c0 c0 r0 r1 (p,x)) (hdb p).1 (hdb p).2
  exact hj.trans ((add_le_add (mul_le_mul_of_nonneg_left h0 (hdb p).1)
    (mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr (hdb p).2))).trans_eq (by ring))

include hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hb1 in
theorem section_memLp (x:HeatCircle):
    @MemLp (ℝ≥0×Ω) (Both RealHaarInput) 𝓕.predictable _ _ (fun p=>Raw (p,x)) 2
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)) := by
  have hs:StronglyMeasurable[𝓕.predictable] (fun p=>Raw (p,x)):=
    (raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd).comp_measurable
      (measurable_id.prodMk measurable_const)
  have hsa:=hs.mono (predictable_le_product 𝓕)
  have hi:Integrable (fun p=>‖Raw (p,x)‖^2) (energyMeasure μ H):=by
    apply (NativePhysicalGammaInput.majorant_integrable 𝓕 v b μ H hbH hb1 (κ:=κ) (U:=U) B).mono'
      (hsa.norm.pow 2).aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 d hdb p x
  have hm:MemLp (fun p=>Raw (p,x)) 2 (energyMeasure μ H):=
    (memLp_two_iff_integrable_sq_norm hsa.aestronglyMeasurable).mpr hi
  change eLpNorm (fun p=>Raw (p,x)) 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))<∞
  rw [eLpNorm_trim (predictable_le_product 𝓕) hs]
  exact hm

def process (x:HeatCircle):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  (section_memLp 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x).toLp
    (fun p=>Raw (p,x))

include hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hb1 in
theorem process_ae (x:HeatCircle):
    process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x=ᵐ[energyMeasure μ H]
      (fun p=>Raw (p,x)):=
  ae_eq_of_ae_eq_trim (section_memLp 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1
    hc0 hc1 hr0 hr1 d hd hdb x).coeFn_toLp

include 𝓕 hg hB hdb hbH hb1 in
theorem parameter_energy_finite :
    (∫⁻x:HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((t,ω),x)‖^2) ∂μ ∂timeMeasure H ∂AddCircle.haarAddCircle)<∞ := by
  haveI:Nonempty Ω:=nonempty_of_isProbabilityMeasure μ
  have hU:0≤U:=elliptic_upper_nonneg (c0 (0,Classical.arbitrary Ω)).1 m U hm (c0 (0,Classical.arbitrary Ω)).2.2
  have hi:=NativePhysicalGammaInput.majorant_integrable 𝓕 v b μ H hbH hb1 (κ:=κ) (U:=U) B
  have htop:(∫⁻p,ENNReal.ofReal (NativePhysicalGammaInput.majorant v b (κ:=κ) (U:=U) B p) ∂energyMeasure μ H)<∞:=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (NativePhysicalGammaInput.majorant_nonneg v b hκ B hU))).mp hi.hasFiniteIntegral
  apply lt_of_le_of_lt _ htop
  calc
    _≤∫⁻x:HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal
        (NativePhysicalGammaInput.majorant v b (κ:=κ) (U:=U) B (t,ω)) ∂μ ∂timeMeasure H ∂AddCircle.haarAddCircle:=by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 d hdb (t,ω) x)
    _=_:=by
      simp only [lintegral_const,measure_univ,mul_one,one_mul]
      exact (lintegral_prod _ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm

include hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hb1 in
/-- Ordinary stochastic Fubini supplies a joint spatial version of the
literal convex joint-Gamma row, driven by the ORIGINAL scalar J. -/
theorem exists_version (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J):
    ∃Y:HeatCircle×Ω→ℝ,Measurable Y ∧
      (∀ᵐx∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ]
        J.integral (process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x)) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)=
        (∫⁻x:HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((t,ω),x)‖^2) ∂μ ∂timeMeasure H ∂AddCircle.haarAddCircle) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)<∞ := by
  have hs:StronglyMeasurable[(inferInstance:MeasurableSpace HeatCircle).prod 𝓕.predictable]
      (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)):=by
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    exact (raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd).comp_measurable measurable_swap
  have hk:=process_ae 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb
  have ht:=parameter_energy_finite 𝓕 v b hκ hm μ H hbH hb1 B hB g hg c0 c1 r0 r1 d hdb
  obtain ⟨Y,hY,hYa,hYe⟩:=StandardItoParameterFubini.energy J hF AddCircle.haarAddCircle
    (process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb)
    (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)) hs hk ht
  exact ⟨Y,hY,hYa,hYe,hYe.trans_lt ht⟩

end SHE.NativeJointPhysicalGammaInput
