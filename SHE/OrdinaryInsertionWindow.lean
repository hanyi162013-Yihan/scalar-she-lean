module
public import SHE.ActualUncutWord

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OrdinaryInsertionWindow
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers UncutWordEvaluation PhysicalIto
local instance ordinaryInsertionWindow_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryInsertionWindow_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryInsertionWindow_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type}[MeasurableSpace P][MeasurableSpace Ω]
variable {R:ReferenceData}{n:ℕ}(L:Level R P n)
variable (U:Ω×ℝ→CircleL2)(X:Ω×(ℝ×HeatCircle)→ℝ)

/-- Exact current-time window conversion, including the null upper
endpoint. This does not require a positive recursive time cutoff. -/
theorem mask_integral {v T b:ℝ}(hv:v≤T)(hT:T≤b)(f:ℝ→ℝ):
    (∫q,if q<T then f q else 0 ∂volume.restrict (Ioc v b))=∫q in v..T,f q:=by
  have he:(fun q:ℝ=>if q<T then f q else 0)=(Iio T).indicator f:=by
    funext q
    simp only [Set.indicator,mem_Iio]
  rw [he,integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hs:Iio T∩Ioc v b=Ioo v T:=by
    ext q
    simp only [mem_inter_iff,mem_Iio,mem_Ioc,mem_Ioo]
    constructor
    · exact fun h=>⟨h.2.1,h.1⟩
    · exact fun h=>⟨h.2,h.1,h.2.le.trans hT⟩
  rw [hs,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hv]

def spatial (a:ℝ→ℝ)(k:ℕ)(p:History P k)(ω:Ω)(q:ℝ):ℝ:=
  ∫y:HeatCircle,insertedWord ((carrier L k).window p) a
    (fun t=>U (ω,t)) (fun z=>X (ω,z)) (UncutSmoothWords.test L k p) q y ∂AddCircle.haarAddCircle

theorem spatial_eq_weight (a:ℝ→ℝ)(k:ℕ)(p:History P k)(ω:Ω)(q:ℝ):
    spatial L U X a k p ω q=UncutSmoothWords.weight L k p*
      ActualUncutWord.spatial (normalizedLevel L k) U X a p ω q:=by
  unfold spatial ActualUncutWord.spatial
  rw [UncutSmoothWords.test_eq_weight_normalized,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y=>ActualUncutWord.inserted_test_smul U X ((carrier L k).window p) a
    (UncutSmoothWords.normalized L k p) (UncutSmoothWords.weight L k p) ω q y)

theorem time_integrable (a:ℝ→ℝ)(ha:Measurable a){A:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)
    (hU:Measurable U)(hX:Measurable X)(k:ℕ)(p:History P k)(ω:Ω):
    IntervalIntegrable (spatial L U X a k p ω) volume R.base ((carrier L k).terminal p):=by
  have hi:=(ActualUncutWord.time_integrable (normalizedLevel L k) U X a ha hAn hA hU hX p ω).const_mul
    (UncutSmoothWords.weight L k p)
  have hf:spatial L U X a k p ω=(fun q=>UncutSmoothWords.weight L k p*
      ActualUncutWord.spatial (normalizedLevel L k) U X a p ω q):=
    funext (spatial_eq_weight L U X a k p ω)
  rw [hf]
  exact hi

/-- The original positive first-hit error equals its uncut physical
current-time integral, with the full word and its true normalization. -/
theorem value_sub_eq_integral (a c:ℝ→ℝ)(ha:Measurable a)(hc:Measurable c)
    {A C:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)(hCn:0≤C)(hC:∀z,|c z|≤C)
    (hU:Measurable U)(hX:Measurable X)(k:ℕ)(p:History P k)(ω:Ω):
    ActualUncutRemainder.value L a U X k p ω-ActualUncutRemainder.value L c U X k p ω=
      ∫q in R.base..(carrier L k).terminal p,
        spatial L U X a k p ω q-spatial L U X c k p ω q:=by
  rw [ActualUncutWord.value_eq_full,ActualUncutWord.value_eq_full]
  simpa only [PhysicalIto.wordRemainder,spatial,Level.window] using (intervalIntegral.integral_sub
    (time_integrable L U X a ha hAn hA hU hX k p ω)
    (time_integrable L U X c hc hCn hC hU hX k p ω)).symm

theorem value_sub_eq_mask (a c:ℝ→ℝ)(ha:Measurable a)(hc:Measurable c)
    {A C:ℝ}(hAn:0≤A)(hA:∀z,|a z|≤A)(hCn:0≤C)(hC:∀z,|c z|≤C)
    (hU:Measurable U)(hX:Measurable X)(k:ℕ)(p:History P k)(ω:Ω):
    ActualUncutRemainder.value L a U X k p ω-ActualUncutRemainder.value L c U X k p ω=
      ∫q,if q<(carrier L k).terminal p then
        spatial L U X a k p ω q-spatial L U X c k p ω q else 0
          ∂volume.restrict (Ioc R.base R.horizon):=by
  rw [mask_integral ((carrier L k).terminal_base p) ((carrier L k).terminal_horizon p)]
  exact value_sub_eq_integral L U X a c ha hc hAn hA hCn hC hU hX k p ω

end SHE.OrdinaryInsertionWindow
