module
public import SHE.NativeJointPhysicalGammaInput
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MovingPhysicalGammaKernel
open Set MeasureTheory FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance movingPhysicalGammaKernel_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingPhysicalGammaKernel_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingPhysicalGammaKernel_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingPhysicalGammaKernel_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingPhysicalGammaKernel_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingPhysicalGammaKernel_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingPhysicalGammaKernel_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingPhysicalGammaKernel_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(past terminal:ℝ→ℝ≥0)
variable (hpast:Measurable past)(hterminal:Measurable terminal)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)
abbrev Domain (Ω:Type*):=(ℝ×(ℝ≥0×Ω))×HeatCircle
variable (g:Fin 6→Domain Ω→ℂ)
variable (hg:∀i,@Measurable (Domain Ω) ℂ
  (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance) _ (g i))
variable (c0 c1 r0 r1:ℝ×(ℝ≥0×Ω)→EllipticField m U)
variable (hc0:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ c0)
variable (hc1:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ c1)
variable (hr0:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ r0)
variable (hr1:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ r1)

def paired (z:Domain Ω):Both RealHaarInput:=
  NativePhysicalGammaKernel.raw (past z.1.1) (terminal z.1.1) hκ hm
    (fun i p=>g i ((z.1.1,p.1),p.2))
    (fun p=>c0 (z.1.1,p)) (fun p=>c1 (z.1.1,p))
    (fun p=>r0 (z.1.1,p)) (fun p=>r1 (z.1.1,p)) (z.1.2,z.2)

include hpast hterminal hg hc0 hc1 hr0 hr1 in
theorem paired_predictable:
    @StronglyMeasurable (Domain Ω) (Both RealHaarInput) _
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance)
      (paired past terminal hκ hm g c0 c1 r0 r1):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have ht:Measurable (fun z:Domain Ω=>(z.1.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_fst.snd
  have hb:Measurable (fun z:Domain Ω=>(terminal z.1.1:ℝ)):=
    NNReal.continuous_coe.measurable.comp (hterminal.comp measurable_fst.fst)
  have hblock (f:ℝ×(ℝ≥0×Ω)→EllipticField m U)(hf:Measurable f):
      Measurable (fun z:Domain Ω=>NativePhysicalGammaKernel.block (terminal z.1.1) hκ hm
        (f z.1) z.1.2 z.2):=by
    have h0:=NativePhysicalRowFields.row_measurable_comp hκ
      (measurable_const (a:=AdditiveHaarForcing.constantField κ hκ)) hb ht measurable_snd
    have h1:=NativePhysicalRowFields.row_measurable_comp hm (hf.comp measurable_fst) hb ht measurable_snd
    exact (WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp (h0.prodMk h1)
  have hn:=(((Complex.continuous_re.measurable.comp (hg 0)).smul (hblock c0 hc0)).sub
    ((Complex.continuous_re.measurable.comp (hg 3)).smul (hblock r0 hr0))).sub
      (((Complex.continuous_re.measurable.comp (hg 2)).smul (hblock c1 hc1)).sub
        ((Complex.continuous_re.measurable.comp (hg 5)).smul (hblock r1 hr1)))
  have hw:MeasurableSet {z:Domain Ω|past z.1.1<z.1.2.1∧z.1.2.1<terminal z.1.1}:=
    (measurableSet_lt (NNReal.continuous_coe.measurable.comp (hpast.comp measurable_fst.fst)) ht).inter
      (measurableSet_lt ht hb)
  exact (hn.ite hw measurable_const).stronglyMeasurable

variable (d:ℝ×(ℝ≥0×Ω)→ℝ)
variable (hd:@Measurable _ _ ((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable) _ d)
def raw (z:Domain Ω):Both RealHaarInput:=
  d z.1 • paired past terminal hκ hm g c0 c1 r0 r1 z+
    (1-d z.1) • paired past terminal hκ hm g c0 c0 r0 r1 z

include hpast hterminal hg hc0 hc1 hr0 hr1 hd in
theorem raw_predictable:
    @StronglyMeasurable (Domain Ω) (Both RealHaarInput) _
      (((inferInstance:MeasurableSpace ℝ).prod 𝓕.predictable).prod inferInstance)
      (raw past terminal hκ hm g c0 c1 r0 r1 d):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have h0:=paired_predictable 𝓕 past terminal hpast hterminal hκ hm g hg c0 c1 r0 r1 hc0 hc1 hr0 hr1
  have h1:=paired_predictable 𝓕 past terminal hpast hterminal hκ hm g hg c0 c0 r0 r1 hc0 hc0 hr0 hr1
  exact ((hd.comp measurable_fst).stronglyMeasurable.smul h0).add
    ((measurable_const.sub (hd.comp measurable_fst)).stronglyMeasurable.smul h1)

theorem raw_section (r:ℝ)(p:ℝ≥0×Ω)(x:HeatCircle):
    raw past terminal hκ hm g c0 c1 r0 r1 d ((r,p),x)=
      NativeJointPhysicalGammaInput.raw (past r) (terminal r) hκ hm
        (fun i p=>g i ((r,p.1),p.2)) (fun p=>c0 (r,p)) (fun p=>c1 (r,p))
        (fun p=>r0 (r,p)) (fun p=>r1 (r,p)) (fun p=>d (r,p)) (p,x):=rfl
end SHE.MovingPhysicalGammaKernel
