module

public import SHE.NativeKernelNashEnergy
public import SHE.ScoreSpatialCauchy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.NativeKernelOutputEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance nativeKernelOutputEnergy_nativePos:Fact (0<2*π):=⟨by positivity⟩
local instance nativeKernelOutputEnergy_unitPos:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeKernelOutputEnergy_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeKernelOutputEnergy_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance nativeKernelOutputEnergy_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeKernelOutputEnergy_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

/-- Integrating a variable OUTPUT L2 amplitude against a positive kernel
uses the input mass, without taking a spatial supremum of that amplitude. -/
theorem weighted_mass {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν:Measure X) [SFinite ν] (ξ:Measure Y) [SFinite ξ]
    (a:X→ℝ) (ha:Measurable a) (hai:Integrable (fun x=>a x^2) ν)
    (k:Y×X→ℝ) (hk:Measurable k) (hk0:∀z,0≤k z) {D E:ℝ} (hD:0≤D)
    (he:(∫x,a x^2 ∂ν)≤E)
    (hcol:∀x,Integrable (fun y=>k (y,x)) ξ ∧ (∫y,k (y,x) ∂ξ)≤D):
    Integrable (fun z:Y×X=>k z*a z.2^2) (ξ.prod ν) ∧
      (∫z:Y×X,k z*a z.2^2 ∂ξ.prod ν)≤D*E:=by
  let G:X×Y→ℝ:=fun z=>k (z.2,z.1)*a z.1^2
  have hGm:Measurable G:=(hk.comp measurable_swap).mul ((ha.comp measurable_fst).pow_const 2)
  have hs(x:X):Integrable (fun y=>G (x,y)) ξ:=by
    change Integrable (fun y=>k (y,x)*a x^2) ξ
    exact (hcol x).1.mul_const _
  have hb(x:X):(∫y,G (x,y) ∂ξ)≤D*a x^2:=by
    change (∫y,k (y,x)*a x^2 ∂ξ)≤_
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hcol x).2 (sq_nonneg _)
  have hmi:Integrable (fun x=>∫y,G (x,y) ∂ξ) ν:=
    (hai.const_mul D).mono' hGm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (ae_of_all _ (fun x=>by
        rw [Real.norm_of_nonneg (integral_nonneg (fun y=>mul_nonneg (hk0 _) (sq_nonneg _)))]
        exact hb x))
  have hGi:Integrable G (ν.prod ξ):=by
    apply (integrable_prod_iff hGm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hs,?_⟩
    have hG0(z:X×Y):0≤G z:=mul_nonneg (hk0 _) (sq_nonneg _)
    simpa only [Real.norm_of_nonneg (hG0 _)] using hmi
  refine ⟨hGi.swap,?_⟩
  have hbnd:(∫z:X×Y,G z ∂ν.prod ξ)≤D*E:=by
    rw [integral_prod _ hGi]
    apply (integral_mono hmi (hai.const_mul D) hb).trans
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left he hD
  convert! (integral_prod_swap G).trans_le hbnd using 1

theorem columnOne_eq_integral {F:Ω×(HeatCircle×HeatCircle)→ℂ}
    (hF:Measurable F) {B:ℝ} (hb:∀ω y x,‖F (ω,(y,x))‖≤B) (ω:Ω) (y:HeatCircle):
    NativeKernelNashEnergy.columnOne F (ω,y)=∫x:HeatCircle,‖F (ω,(y,x))‖ ∂haarAddCircle:=by
  rw [NativeKernelNashEnergy.columnOne,NativeKernelNashEnergy.unitRow,NativeKernelNashEnergy.unitColumns]
  rw [RandomRowEnergy.row_normOne
    (NativeRandomRows.unitField_measurable (NativeRandomKernel.columnField_measurable hF))
    (fun p x=>hb p.1 p.2 _)]
  exact (CircleNormalization.scale_measurePreserving 1 (2*π)).integral_comp
    (CircleNormalization.scaleMeasurableEquiv 1 (2*π)).measurableEmbedding
    (fun x:HeatCircle=>‖F (ω,(y,x))‖)

/-- A true RMS kernel bound with an arbitrary spatial L2 output amplitude
implies the actual native negative Hilbert kernel energy. Both column
masses are derived, so this theorem needs no assumed trace or column cap. -/
theorem from_rms_envelope (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    (a:HeatCircle→ℝ) (ha:Measurable a) (ha0:∀x,0≤a x)
    (hai:Integrable (fun x=>a x^2) haarAddCircle) {E J:ℝ}
    (he:(∫x,a x^2 ∂haarAddCircle)≤E) (hJ:0≤J)
    (k:HeatCircle×HeatCircle→ℝ) (hk:Measurable k) (hk0:∀z,0≤k z)
    (hrow:∀y,Integrable (fun x=>k (y,x)) haarAddCircle ∧ (∫x,k (y,x) ∂haarAddCircle)=1)
    (hcol:∀x,Integrable (fun y=>k (y,x)) haarAddCircle ∧ (∫y,k (y,x) ∂haarAddCircle)≤1)
    (hsq:∀x,Integrable (fun y=>k (y,x)^2) haarAddCircle ∧ (∫y,k (y,x)^2 ∂haarAddCircle)≤J)
    (hsharp:∀y x,ProfileL2.normTwo μ (fun ω=>‖F (ω,(y,x))‖)≤a x*k (y,x))
    {Λ ρ t:ℝ} (hΛ:1≤Λ) (hρ:0<ρ) (hρhalf:ρ<1/2) (ht:0<t) (ht1:t≤1):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeHeatSpan.clock t)^(ρ-1/2))*E+
          (NativeHeatSpan.clock t)^ρ*(J*E):=by
  have hm1:=weighted_mass haarAddCircle haarAddCircle a ha hai k hk hk0 (by norm_num) he hcol
  have hm2:=weighted_mass haarAddCircle haarAddCircle a ha hai (fun z=>k z^2)
    (hk.pow_const 2) (fun _=>sq_nonneg _) hJ he hsq
  let L:=fun p:Ω×HeatCircle=>NativeKernelNashEnergy.columnOne F p
  have hLm:Measurable L:=by
    have heq:L=(fun p=>∫x:HeatCircle,‖F (p.1,(p.2,x))‖ ∂haarAddCircle):=
      funext (fun p=>columnOne_eq_integral hF hb p.1 p.2)
    rw [heq]
    exact ((hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).norm).stronglyMeasurable.integral_prod_right'.measurable
  have hLi:Integrable (fun p=>L p^2) (μ.prod haarAddCircle):=by
    apply (integrable_const (B^2)).mono' (hLm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun p=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (HeatMarkov.normOne_nonneg _) _ 2
      change L p≤B
      rw [show L p=∫x:HeatCircle,‖F (p.1,(p.2,x))‖ ∂haarAddCircle from columnOne_eq_integral hF hb p.1 p.2]
      exact (integral_mono_of_nonneg (ae_of_all _ (fun _=>norm_nonneg _))
        (integrable_const B) (ae_of_all _ (hb p.1 p.2))).trans_eq (by simp))
  have hM1:(∫p:Ω×HeatCircle,L p^2 ∂μ.prod haarAddCircle)≤E:=by
    have hs:∀ᵐy:HeatCircle∂haarAddCircle,
        (∫ω,L (ω,y)^2 ∂μ)≤∫x,k (y,x)*a x^2 ∂haarAddCircle:=by
      filter_upwards [(integrable_prod_iff hm1.1.aestronglyMeasurable).mp hm1.1 |>.1] with y hy
      have hcs:=ScoreSpatialCauchy.weighted_sqrt_integral haarAddCircle (fun x=>k (y,x))
        (fun x=>a x^2) (hrow y).1 hy (ha.pow_const 2)
        (ae_of_all _ (fun x=>hk0 (y,x))) (fun _=>sq_nonneg _)
      have hsqrt(x:HeatCircle):Real.sqrt (a x^2)=a x:=Real.sqrt_sq (ha0 x)
      simp_rw [hsqrt] at hcs
      have hkm:Integrable (fun x=>a x*k (y,x)) haarAddCircle:=by
        simpa only [mul_comm] using hcs.1
      have hMi:=ProfileL2.bounded_minkowski_two (μ:=haarAddCircle) (ν:=μ)
        (F:=fun p:HeatCircle×Ω=>‖F (p.2,(y,p.1))‖) (a:=fun x=>a x*k (y,x)) (b:=fun _=>B)
        ((hF.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).norm)
        hkm (integrable_const B) (ae_of_all _ (fun x=>mul_nonneg (ha0 x) (hk0 _)))
        (ae_of_all _ (fun _=>hB))
        (ae_of_all _ (fun x ω=>by rw [abs_of_nonneg (norm_nonneg _)]; exact hb ω y x))
        (ae_of_all _ (fun x=>hsharp y x))
      have hMi':Real.sqrt (∫ω,L (ω,y)^2 ∂μ)≤∫x,k (y,x)*a x ∂haarAddCircle:=by
        simpa only [ProfileL2.normTwo,←columnOne_eq_integral hF hb,mul_comm,L] using hMi
      have hcap:=hMi'.trans (by simpa only [(hrow y).2,Real.sqrt_one,one_mul] using hcs.2)
      have hh:=pow_le_pow_left₀ (Real.sqrt_nonneg _) hcap 2
      rwa [Real.sq_sqrt (integral_nonneg (fun _=>sq_nonneg _)),
        Real.sq_sqrt (integral_nonneg (fun x=>mul_nonneg (hk0 _) (sq_nonneg _)))] at hh
    rw [integral_prod _ hLi,integral_integral_swap hLi]
    apply (integral_mono_ae hLi.integral_prod_right hm1.1.integral_prod_left hs).trans
    rw [←integral_prod _ hm1.1]
    simpa only [one_mul] using hm1.2
  have hM2:(∫p:Ω×HeatCircle,‖NativeRandomKernel.column F p‖^2 ∂μ.prod haarAddCircle)≤J*E:=by
    have hfi:Integrable (fun z:Ω×(HeatCircle×HeatCircle)=>‖F z‖^2) (μ.prod (haarAddCircle.prod haarAddCircle)):=
      (integrable_const (B^2)).mono' (hF.norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ (fun z=>by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hb z.1 z.2.1 z.2.2) 2))
    have hc(ω:Ω)(y:HeatCircle):‖NativeRandomKernel.column F (ω,y)‖^2=
        ∫x:HeatCircle,‖F (ω,(y,x))‖^2 ∂haarAddCircle:=by
      rw [StoppedFourier.L2_norm_sq_eq_integral]
      exact integral_congr_ae ((NativeRandomKernel.column_ae hF hb ω y).mono (fun x hx=>by
        change ‖NativeRandomKernel.column F (ω,y) x‖^2=‖F (ω,(y,x))‖^2
        rw [hx]))
    simp_rw [hc]
    have hrec:Integrable (fun z:(Ω×HeatCircle)×HeatCircle=>‖F (z.1.1,(z.1.2,z.2))‖^2)
        ((μ.prod haarAddCircle).prod haarAddCircle):=
      (measurePreserving_prodAssoc μ haarAddCircle haarAddCircle).integrable_comp_of_integrable hfi
    rw [integral_prod _ hrec.integral_prod_left]
    have heq(ω:Ω):(∫y:HeatCircle,∫x:HeatCircle,‖F (ω,(y,x))‖^2 ∂haarAddCircle ∂haarAddCircle)=
        ∫z:HeatCircle×HeatCircle,‖F (ω,z)‖^2 ∂haarAddCircle.prod haarAddCircle:=by
      have hi:Integrable (fun z:HeatCircle×HeatCircle=>‖F (ω,z)‖^2) (haarAddCircle.prod haarAddCircle):=
        (integrable_const (B^2)).mono'
        ((hF.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ (fun z=>by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hb ω z.1 z.2) 2))
      exact (integral_prod (fun z:HeatCircle×HeatCircle=>‖F (ω,z)‖^2) hi).symm
    simp_rw [heq]
    rw [integral_integral_swap hfi]
    apply (integral_mono_ae hfi.integral_prod_right hm2.1 (ae_of_all _ (fun z=>?_))).trans hm2.2
    have hh:=pow_le_pow_left₀ (ProfileL2.normTwo_nonneg μ _) (hsharp z.1 z.2) 2
    rw [ProfileL2.normTwo,Real.sq_sqrt (integral_nonneg (fun _=>sq_nonneg _)),mul_pow] at hh
    simpa only [mul_comm] using hh
  exact NativeKernelNashEnergy.from_column_masses μ hF hB hb hΛ hρ hρhalf ht ht1 hLi hM1 hM2

end SHE.NativeKernelOutputEnergy
