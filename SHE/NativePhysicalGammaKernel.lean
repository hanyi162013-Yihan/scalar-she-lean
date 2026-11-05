module

public import SHE.NativePhysicalRowFields
public import SHE.NativeGammaClock
public import SHE.ScalarHeatGammaSlots
public import SHE.AdditiveHaarForcing
public import SHE.OrthogonalItoChannels
public import SHE.StandardItoParameterFubini

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativePhysicalGammaKernel
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v b:ℝ≥0)
variable {κ m U:ℝ} (hκ:0<κ) (hm:0<m)

def block (f:EllipticField m U) (p:ℝ≥0×Ω) (x:HeatCircle):Both RealHaarInput:=
  WithLp.toLp 2 (row hκ (AdditiveHaarForcing.constantField κ hκ) b p.1 x,row hm f b p.1 x)

def raw (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
    (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U) (z:(ℝ≥0×Ω)×HeatCircle):Both RealHaarInput:=by
  classical
  exact if z.1∈NativeGammaClock.window v b then
    ((g 0 z).re • block b hκ hm (c0 z.1) z.1 z.2-(g 3 z).re • block b hκ hm (r0 z.1) z.1 z.2)-
      ((g 2 z).re • block b hκ hm (c1 z.1) z.1 z.2-(g 5 z).re • block b hκ hm (r1 z.1) z.1 z.2)
  else 0

/-- Joint predictability in the ORIGINAL noise/sample variables and
Borel measurability in the actual physical output center. -/
theorem raw_predictable (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
    (hg:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
    (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
    (hc0:Measurable[𝓕.predictable] c0) (hc1:Measurable[𝓕.predictable] c1)
    (hr0:Measurable[𝓕.predictable] r0) (hr1:Measurable[𝓕.predictable] r1):
    StronglyMeasurable[𝓕.predictable.prod inferInstance] (raw v b hκ hm g c0 c1 r0 r1):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have htime:Measurable (fun z:(ℝ≥0×Ω)×HeatCircle=>(z.1.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_fst
  have hbmeas (f:ℝ≥0×Ω→EllipticField m U)(hf:Measurable f):
      Measurable (fun z:(ℝ≥0×Ω)×HeatCircle=>block b hκ hm (f z.1) z.1 z.2):=by
    have h0:=NativePhysicalRowFields.row_measurable_comp hκ
      (measurable_const (a:=AdditiveHaarForcing.constantField κ hκ)) (measurable_const (a:=(b:ℝ))) htime measurable_snd
    have h1:=NativePhysicalRowFields.row_measurable_comp hm (hf.comp measurable_fst)
      (measurable_const (a:=(b:ℝ))) htime measurable_snd
    exact (WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp (h0.prodMk h1)
  have hn:=(((Complex.continuous_re.measurable.comp (hg 0)).smul (hbmeas c0 hc0)).sub
      ((Complex.continuous_re.measurable.comp (hg 3)).smul (hbmeas r0 hr0))).sub
    (((Complex.continuous_re.measurable.comp (hg 2)).smul (hbmeas c1 hc1)).sub
      ((Complex.continuous_re.measurable.comp (hg 5)).smul (hbmeas r1 hr1)))
  exact (hn.ite ((NativeGammaClock.window_measurable 𝓕 v b).preimage measurable_fst) measurable_const).stronglyMeasurable

theorem block_norm_sq (f:EllipticField m U) (p:ℝ≥0×Ω) (hp:p∈NativeGammaClock.window v b) (x:HeatCircle):
    ‖block b hκ hm f p x‖^2≤(κ+U)*(1+heatConstant*(NativeGammaClock.age v b p)^(-(1/2:ℝ))):=by
  have ht:(p.1:ℝ)<(b:ℝ):=by exact_mod_cast hp.2
  have h0:=NativeObservationProcess.row_norm_sq_bound hκ (AdditiveHaarForcing.constantField κ hκ) ht le_rfl x
  have h1:=NativeObservationProcess.row_norm_sq_bound hm f ht le_rfl x
  change ‖WithLp.toLp 2 (_,_)‖^2≤_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  have he:NativeGammaClock.age v b p=(b:ℝ)-(p.1:ℝ):=if_pos hp
  rw [he]
  change ‖row hκ (AdditiveHaarForcing.constantField κ hκ) b p.1 x‖^2+
    ‖row hm f b p.1 x‖^2≤_
  nlinarith [h0,h1]

theorem four_norm_sq {E:Type*} [NormedAddCommGroup E] (a b c d:E):
    ‖(a-b)-(c-d)‖^2≤4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2):=by
  have hn:‖(a-b)-(c-d)‖≤‖a‖+‖b‖+‖c‖+‖d‖:=
    (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) (norm_sub_le _ _)).trans_eq (by ring))
  have hs:=pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (‖b‖-‖c‖),sq_nonneg (‖b‖-‖d‖),sq_nonneg (‖c‖-‖d‖)]

/-- A coarse integrable heat singularity supplies stochastic Fubini
applicability. This is separate from the sharp six-slot bound. -/
theorem raw_norm_sq {B:ℝ} (hB:0≤B) (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
    (hg:∀i p x,‖g i (p,x)‖≤B) (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
    (p:ℝ≥0×Ω) (hp:p∈NativeGammaClock.window v b) (x:HeatCircle):
    ‖raw v b hκ hm g c0 c1 r0 r1 (p,x)‖^2≤
      16*B^2*(κ+U)*(1+heatConstant*(NativeGammaClock.age v b p)^(-(1/2:ℝ))):=by
  have hU:0≤U:=elliptic_upper_nonneg (c0 p).1 m U hm (c0 p).2.2
  let C:=(κ+U)*(1+heatConstant*(NativeGammaClock.age v b p)^(-(1/2:ℝ)))
  have hC:0≤C:=mul_nonneg (add_nonneg hκ.le hU)
    (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (NativeGammaClock.age_pos v b p).le _)))
  have hs(i:Fin 6)(f:EllipticField m U):‖(g i (p,x)).re • block b hκ hm f p x‖^2≤B^2*C:=by
    rw [norm_smul,mul_pow]
    have hb:‖(g i (p,x)).re‖≤B:=by
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm (g i (p,x))).trans (hg i p x)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb 2)
      (block_norm_sq v b hκ hm f p hp x) (sq_nonneg _) (sq_nonneg _)
  rw [raw,if_pos hp]
  have hn:=four_norm_sq ((g 0 (p,x)).re • block b hκ hm (c0 p) p x)
    ((g 3 (p,x)).re • block b hκ hm (r0 p) p x)
    ((g 2 (p,x)).re • block b hκ hm (c1 p) p x)
    ((g 5 (p,x)).re • block b hκ hm (r1 p) p x)
  have hsum:=add_le_add (add_le_add (add_le_add (hs 0 (c0 p)) (hs 3 (r0 p))) (hs 2 (c1 p))) (hs 5 (r1 p))
  dsimp only [C] at *
  nlinarith [hsum]

end SHE.NativePhysicalGammaKernel
