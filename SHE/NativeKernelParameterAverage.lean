module
public import SHE.NativeRandomKernel
public import SHE.HilbertFiniteAverage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
namespace SHE.NativeKernelParameterAverage
open Set MeasureTheory ProbabilityTheory StoppedFourier
open scoped ENNReal InnerProductSpace
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : Fact ((1:ENNReal)≤2):=⟨by norm_num⟩
local instance : SecondCountableTopology CircleL2:=
  Lp.SecondCountableTopology
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology NativeRandomKernel.KernelSpace:=Lp.SecondCountableTopology
local instance : MeasurableSpace NativeRandomKernel.KernelSpace:=borel _
local instance : BorelSpace NativeRandomKernel.KernelSpace:=⟨rfl⟩

private theorem lp_integral {W X E:Type*} [MeasurableSpace W] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν:Measure W) [IsProbabilityMeasure ν] (ξ:Measure X) [IsProbabilityMeasure ξ]
    [SecondCountableTopology (Lp E 2 ξ)]
    [MeasurableSpace (Lp E 2 ξ)] [BorelSpace (Lp E 2 ξ)]
    (F:W×X→E) (hF:Measurable F) {B:ℝ} (hB:0≤B) (hb:∀w x,‖F (w,x)‖≤B)
    (K:W→Lp E 2 ξ) (hK:Measurable K) (hKb:∀w,‖K w‖≤B)
    (hKr:∀w,K w=ᵐ[ξ] fun x=>F (w,x))
    (Kavg:Lp E 2 ξ) (havg:Kavg=ᵐ[ξ] fun x=>∫w,F (w,x) ∂ν):
    Kavg=∫w,K w ∂ν:=by
  have hKi:Integrable K ν:=(integrable_const B).mono' hK.aestronglyMeasurable (ae_of_all _ hKb)
  have hFi(x:X):Integrable (fun w=>F (w,x)) ν:=(integrable_const B).mono'
    (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable (ae_of_all _ (fun w=>hb w x))
  apply ext_inner_left ℂ
  intro Z
  have hZi:Integrable (fun x=>‖Z x‖) ξ:=((Lp.memLp Z).integrable (by norm_num : (1:ENNReal)≤2)).norm
  have hIm:Measurable (fun z:W×X=>inner ℂ (Z z.2) (F z)):=
    continuous_inner.measurable.comp
      (((Lp.stronglyMeasurable Z).measurable.comp measurable_snd).prodMk hF)
  have hIi:Integrable (fun z:W×X=>inner ℂ (Z z.2) (F z)) (ν.prod ξ):=
    ((hZi.comp_snd ν).const_mul B).mono' hIm.aestronglyMeasurable (ae_of_all _ (fun z=>
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (Z z.2),hb z.1 z.2])))
  calc
    inner ℂ Z Kavg=∫x,inner ℂ (Z x) (Kavg x) ∂ξ:=L2.inner_def _ _
    _=∫x,inner ℂ (Z x) (∫w,F (w,x) ∂ν) ∂ξ:=integral_congr_ae
      (havg.mono (fun x hx=>congrArg (fun e=>inner ℂ (Z x) e) hx))
    _=∫x,∫w,inner ℂ (Z x) (F (w,x)) ∂ν ∂ξ:=by
      apply integral_congr_ae
      exact ae_of_all _ (fun x=>((innerSL ℂ (Z x)).integral_comp_comm (hFi x)).symm)
    _=∫w,∫x,inner ℂ (Z x) (F (w,x)) ∂ξ ∂ν:=(integral_integral_swap hIi).symm
    _=∫w,inner ℂ Z (K w) ∂ν:=by
      apply integral_congr_ae
      exact ae_of_all _ (fun w=>by
        change (∫x,inner ℂ (Z x) (F (w,x)) ∂ξ)=inner ℂ Z (K w)
        rw [L2.inner_def]
        exact integral_congr_ae ((hKr w).mono (fun x hx=>congrArg (fun e=>inner ℂ (Z x) e) hx.symm)))
    _=inner ℂ Z (∫w,K w ∂ν):=(innerSL ℂ Z).integral_comp_comm hKi

variable {W:Type*} [MeasurableSpace W] (ν:Measure W) [IsProbabilityMeasure ν]

def average (F:W×(HeatCircle×HeatCircle)→ℂ) (z:Unit×(HeatCircle×HeatCircle)):ℂ:=
  ∫w,F (w,z.2) ∂ν

theorem average_measurable {F:W×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F):
    Measurable (average ν F):=
  hF.stronglyMeasurable.integral_prod_left'.measurable.comp measurable_snd

theorem average_bound {F:W×(HeatCircle×HeatCircle)→ℂ} {B:ℝ}
    (hb:∀w y x,‖F (w,(y,x))‖≤B) (u:Unit) (y x:HeatCircle):
    ‖average ν F (u,(y,x))‖≤B:=by
  exact (norm_integral_le_integral_norm _).trans
    ((integral_mono_of_nonneg (ae_of_all _ (fun _=>norm_nonneg _)) (integrable_const B)
      (ae_of_all _ (fun w=>hb w y x))).trans_eq (by simp))

/-- An actual bounded physical kernel commutes with positive old-space
averaging in the native L2 columns. -/
theorem column_average {F:W×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀w y x,‖F (w,(y,x))‖≤B) (y:HeatCircle):
    NativeRandomKernel.column (average ν F) ((),y)=∫w,NativeRandomKernel.column F (w,y) ∂ν:=by
  have ha:=average_measurable ν hF
  have hab:=average_bound ν hb
  refine lp_integral ν (AddCircle.haarAddCircle (T:=2*Real.pi)) (fun z:W×HeatCircle=>F (z.1,(y,z.2)))
    (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) hB (fun w x=>hb w y x)
    (fun w=>NativeRandomKernel.column F (w,y))
    ((NativeRandomKernel.column_measurable hF hb).comp (measurable_id.prodMk measurable_const))
    (fun w=>NativeRandomKernel.column_norm_le hF hB hb (w,y))
    (fun w=>NativeRandomKernel.column_ae hF hb w y)
    (NativeRandomKernel.column (average ν F) ((),y)) ?_
  exact NativeRandomKernel.column_ae ha hab () y

/-- The genuine native negative-output kernel of the ORIGINAL scalar
old-space average is the Hilbert average of the point negative kernels.
The Bessel output map and both spatial realizations are derived here. -/
theorem negative_average {F:W×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀w y x,‖F (w,(y,x))‖≤B)
    {Λ ρ:ℝ} (hΛ:1≤Λ) (hρ:0≤ρ):
    NativeRandomKernel.negativeKernel Λ ρ hΛ hρ (average ν F) ()=
      ∫w,NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F w ∂ν:=by
  have ha:=average_measurable ν hF
  have hab:=average_bound ν hb
  have hc(y:HeatCircle):NativeRandomKernel.negativeColumn Λ ρ hΛ hρ (average ν F) ((),y)=
      ∫w,NativeRandomKernel.negativeColumn Λ ρ hΛ hρ F (w,y) ∂ν:=by
    unfold NativeRandomKernel.negativeColumn
    rw [column_average ν hF hB hb y]
    exact ((OneInputOperator.besselHalf Λ ρ hΛ hρ).integral_comp_comm
      ((integrable_const B).mono'
        (((NativeRandomKernel.column_measurable hF hb).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (ae_of_all _ (fun w=>NativeRandomKernel.column_norm_le hF hB hb (w,y))))).symm
  refine lp_integral ν (AddCircle.haarAddCircle (T:=2*Real.pi))
    (fun z:W×HeatCircle=>NativeRandomKernel.negativeColumn Λ ρ hΛ hρ F z)
    (NativeRandomKernel.negativeColumn_measurable hΛ hρ hF hb) hB
    (fun w y=>NativeRandomKernel.negativeColumn_norm_le hΛ hρ hF hB hb (w,y))
    (NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F)
    (NativeRandomKernel.negativeKernel_measurable hΛ hρ hF hB hb)
    (fun w=>by
      have hh:=Lp.norm_le_of_ae_bound hB ((NativeRandomKernel.negativeKernel_ae hΛ hρ hF hB hb w).mono
        (fun y hy=>by rw [hy];exact NativeRandomKernel.negativeColumn_norm_le hΛ hρ hF hB hb (w,y)))
      simpa [measureUnivNNReal] using hh)
    (fun w=>NativeRandomKernel.negativeKernel_ae hΛ hρ hF hB hb w)
    (NativeRandomKernel.negativeKernel Λ ρ hΛ hρ (average ν F) ()) ?_
  filter_upwards [NativeRandomKernel.negativeKernel_ae hΛ hρ ha hB hab ()] with y hy
  exact hy.trans (hc y)

variable {Ω:Type*} [MeasurableSpace Ω]

def spatialAverage (F:(W×Ω)×(HeatCircle×HeatCircle)→ℂ)
    (z:Ω×(HeatCircle×HeatCircle)):ℂ:=∫w,F ((w,z.1),z.2) ∂ν

/-- Native old-space Minkowski for the LITERAL original scalar average.
The output Bessel map is not assumed to commute with that average: its
exact equality is supplied by negative_average above. -/
theorem energy (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:(W×Ω)×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀p y x,‖F (p,(y,x))‖≤B)
    {Λ ρ:ℝ} (hΛ:1≤Λ) (hρ:0≤ρ)
    (A:W→ℝ) (hAm:Measurable A) (hAi:Integrable A ν) (hA:∀w,0≤A w)
    (hi:∀ᵐw∂ν,Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F (w,ω)‖^2) μ)
    (he:∀ᵐw∂ν,(∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F (w,ω)‖^2 ∂μ)≤A w^2):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ (spatialAverage ν F) ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ (spatialAverage ν F) ω‖^2 ∂μ)≤
        (∫w,A w ∂ν)^2:=by
  have hm:=NativeRandomKernel.negativeKernel_measurable hΛ hρ hF hB hb
  have henergy:=HilbertParameterAverage.finite_energy μ ν
    (fun z:W×Ω=>NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F z) hm A hAm hAi hA hi he
  have hid(ω:Ω):NativeRandomKernel.negativeKernel Λ ρ hΛ hρ (spatialAverage ν F) ω=
      ∫w,NativeRandomKernel.negativeKernel Λ ρ hΛ hρ F (w,ω) ∂ν:=by
    have hsection:Measurable (fun z:W×(HeatCircle×HeatCircle)=>F ((z.1,ω),z.2)):=
      hF.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have hh:=negative_average ν hsection hB (fun w y x=>hb (w,ω) y x) hΛ hρ
    convert! hh using 1
  simpa only [hid] using henergy.2

end SHE.NativeKernelParameterAverage
