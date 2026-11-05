module

public import SHE.NativeRandomRows
public import SHE.HilbertL2Fields
public import SHE.KernelAdjoint

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeRandomKernel_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeRandomKernel_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeRandomKernel_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance nativeRandomKernel_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeRandomKernel_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

abbrev KernelSpace := Lp CircleL2 2 (haarAddCircle (T:=2*π))
local instance nativeRandomKernel_kernelSecondCountable : SecondCountableTopology KernelSpace :=
  Lp.SecondCountableTopology
local instance nativeRandomKernel_kernelMeasurable : MeasurableSpace KernelSpace := borel KernelSpace
local instance nativeRandomKernel_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first spatial variable is the input location; the second is
the output location. No random dependence is removed by this regrouping. -/
def columnField (F : Ω × (HeatCircle × HeatCircle) → ℂ)
    (p : (Ω × HeatCircle) × HeatCircle) : ℂ := F (p.1.1,(p.1.2,p.2))

def column (F : Ω × (HeatCircle × HeatCircle) → ℂ) (p : Ω × HeatCircle) : CircleL2 :=
  NativeRandomRows.nativeRow (columnField F) p

theorem columnField_measurable {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) : Measurable (columnField F) :=
  hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

theorem column_measurable {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) :
    Measurable (column F) :=
  NativeRandomRows.nativeRow_measurable (columnField_measurable hF) (fun p x => hb p.1 p.2 x)

theorem column_ae {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (ω : Ω) (y : HeatCircle) : (column F (ω,y) : HeatCircle → ℂ)=ᵐ[haarAddCircle]
      fun x => F (ω,(y,x)) :=
  NativeRandomRows.nativeRow_ae (columnField_measurable hF) (fun p x => hb p.1 p.2 x) (ω,y)

theorem column_norm_le {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (p : Ω × HeatCircle) : ‖column F p‖ ≤ B := by
  have h := Lp.norm_le_of_ae_bound hB ((column_ae hF hb p.1 p.2).mono (fun x hx => by
    change column F p x=F (p.1,(p.2,x)) at hx
    rw [hx]
    exact hb p.1 p.2 x))
  simpa [measureUnivNNReal] using h

/-- The original, unsmoothed random integral kernel. -/
def kernel (F : Ω × (HeatCircle × HeatCircle) → ℂ) (ω : Ω) : KernelSpace :=
  HilbertL2Fields.realize (column F) ω

theorem column_memLp {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    MemLp (fun y => column F (ω,y)) 2 haarAddCircle :=
  MemLp.of_bound ((column_measurable hF hb).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
    (ae_of_all _ (fun y => column_norm_le hF hB hb (ω,y)))

theorem kernel_ae {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    (kernel F ω : HeatCircle → CircleL2)=ᵐ[haarAddCircle] fun y => column F (ω,y) :=
  HilbertL2Fields.realize_ae _ (column_memLp hF hB hb) ω

theorem kernel_measurable {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) : Measurable (kernel F) :=
  HilbertL2Fields.realize_measurable (column_measurable hF hb) (column_memLp hF hB hb)

def integralOperator (F : Ω × (HeatCircle × HeatCircle) → ℂ) (ω : Ω) : CircleL2 →L[ℂ] CircleL2 :=
  KernelOperator.synthesis (kernel F ω)

/-- The operator is genuinely synthesized by integrating the original
physical spatial L² columns, with their input signs intact. -/
theorem integralOperator_eq_integral {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) (v : CircleL2) :
    integralOperator F ω v = ∫ y, v y • column F (ω,y) ∂haarAddCircle := by
  rw [integralOperator,KernelOperator.synthesis_eq_integral]
  exact integral_congr_ae ((kernel_ae hF hB hb ω).mono (fun y hy => by
    change v y • kernel F ω y=v y • column F (ω,y)
    change kernel F ω y=column F (ω,y) at hy
    rw [hy]))

/-- Actual negative-output kernel columns. -/
def negativeColumn (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (F : Ω × (HeatCircle × HeatCircle) → ℂ) (p : Ω × HeatCircle) : CircleL2 :=
  OneInputOperator.besselHalf Λ ρ hΛ hρ (column F p)

theorem negativeColumn_measurable {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) :
    Measurable (negativeColumn Λ ρ hΛ hρ F) :=
  (OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp (column_measurable hF hb)

theorem negativeColumn_norm_le {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (p : Ω × HeatCircle) :
    ‖negativeColumn Λ ρ hΛ hρ F p‖ ≤ B :=
  (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _).trans (column_norm_le hF hB hb p)

def negativeKernel (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (F : Ω × (HeatCircle × HeatCircle) → ℂ) (ω : Ω) : KernelSpace :=
  HilbertL2Fields.realize (negativeColumn Λ ρ hΛ hρ F) ω

theorem negativeColumn_memLp {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    MemLp (fun y => negativeColumn Λ ρ hΛ hρ F (ω,y)) 2 haarAddCircle :=
  MemLp.of_bound ((negativeColumn_measurable hΛ hρ hF hb).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
    (ae_of_all _ (fun y => negativeColumn_norm_le hΛ hρ hF hB hb (ω,y)))

theorem negativeKernel_ae {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    (negativeKernel Λ ρ hΛ hρ F ω : HeatCircle → CircleL2)=ᵐ[haarAddCircle]
      fun y => negativeColumn Λ ρ hΛ hρ F (ω,y) :=
  HilbertL2Fields.realize_ae _ (negativeColumn_memLp hΛ hρ hF hB hb) ω

theorem negativeKernel_measurable {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) :
    Measurable (negativeKernel Λ ρ hΛ hρ F) :=
  HilbertL2Fields.realize_measurable (negativeColumn_measurable hΛ hρ hF hb)
    (negativeColumn_memLp hΛ hρ hF hB hb)

theorem negativeKernel_eq_compLp {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    negativeKernel Λ ρ hΛ hρ F ω=
      (OneInputOperator.besselHalf Λ ρ hΛ hρ).compLp (kernel F ω) := by
  apply Lp.ext
  filter_upwards [negativeKernel_ae hΛ hρ hF hB hb ω,kernel_ae hF hB hb ω,
    (OneInputOperator.besselHalf Λ ρ hΛ hρ).coeFn_compLp (kernel F ω)] with y hn hk hq
  rw [hn,hq,hk]
  rfl

/-- The negative-output synthesis is exactly Q^(1/2) composed with the
original signed integral operator. -/
theorem negative_synthesis_eq {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (ω : Ω) :
    KernelOperator.synthesis (negativeKernel Λ ρ hΛ hρ F ω)=
      (OneInputOperator.besselHalf Λ ρ hΛ hρ).comp (integralOperator F ω) := by
  rw [negativeKernel_eq_compLp hΛ hρ hF hB hb ω,KernelOperator.synthesis_compLp]
  rfl

/-- A sharp RMS heat envelope gives a genuine expected Hilbert-valued
kernel mass estimate. The coarse pointwise bound appears only in the
proved measurability and Fubini applicability. -/
theorem expected_negativeKernel_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    {Λ ρ t K : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (center : HeatCircle → HeatCircle)
    (hsharp : ∀ y x, ProfileL2.normTwo μ (fun ω => ‖F (ω,(y,x))‖) ≤
      K*‖ProfileVariance.heatPhysical (8*t) (center y) x‖) :
    Integrable (fun ω => ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ ω, ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ) ≤
        GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*K^2 ∧
      (∫ ω, ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ) ≤
        GaussianNegativePacket.traceConstant*Λ^(-ρ)*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*K^2 := by
  have hs (y : HeatCircle) := NativeRandomRows.expected_dominated_negative μ
    (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) hB
    (fun ω x => hb ω y x) hΛ hρ hρhalf ht ht1 hK (center y) (hsharp y)
  have hfirst := HilbertL2Fields.expected_norm_sq_bound (ν:=haarAddCircle (T:=2*π)) μ
    (negativeColumn_measurable hΛ hρ.le hF hb)
    (fun ω y => negativeColumn_norm_le hΛ hρ.le hF hB hb (ω,y))
    (fun y => (hs y).2.1)
  have hsecond := HilbertL2Fields.expected_norm_sq_bound (ν:=haarAddCircle (T:=2*π)) μ
    (negativeColumn_measurable hΛ hρ.le hF hb)
    (fun ω y => negativeColumn_norm_le hΛ hρ.le hF hB hb (ω,y))
    (fun y => (hs y).2.2)
  exact ⟨hfirst.1,hfirst.2,hsecond.2⟩

/-- Expected negative-output Hilbert--Schmidt energy of the actual
random integral operator, retaining an arbitrary dependent bounded noise
factor. All trace measurability and integrability are derived from the
joint scalar field and the genuine measurable noise columns. -/
theorem expected_negative_right_trace
    {G N : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Countable N] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    {Λ ρ t K C : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (center : HeatCircle → HeatCircle)
    (hsharp : ∀ y x, ProfileL2.normTwo μ (fun ω => ‖F (ω,(y,x))‖) ≤
      K*‖ProfileVariance.heatPhysical (8*t) (center y) x‖)
    (R : Ω → G →L[ℂ] CircleL2) (g : HilbertBasis N ℂ G)
    (hC : 0 ≤ C) (hR : ∀ ω, ‖R ω‖^2 ≤ C)
    (hRmeas : ∀ n, Measurable (fun ω => R ω (g n))) :
    Integrable (fun ω => ∑' n, ‖((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp
      ((integralOperator F ω).comp (R ω))) (g n)‖^2) μ ∧
      (∫ ω, ∑' n, ‖((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp
        ((integralOperator F ω).comp (R ω))) (g n)‖^2 ∂μ) ≤
        C*(GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*K^2) ∧
      (∫ ω, ∑' n, ‖((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp
        ((integralOperator F ω).comp (R ω))) (g n)‖^2 ∂μ) ≤
        C*(GaussianNegativePacket.traceConstant*Λ^(-ρ)*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*K^2) := by
  have hk := expected_negativeKernel_bound μ hF hB hb hΛ hρ hρhalf ht ht1 hK center hsharp
  have hm := negativeKernel_measurable hΛ hρ.le hF hB hb
  have hfirst := KernelOperator.expected_synthesis_right_trace_bound μ
    (negativeKernel Λ ρ hΛ hρ.le F) R (fourierBasis (T:=2*π)) (fourierBasis (T:=2*π)) g
    hm hRmeas hC hR hk.1 hk.2.1
  have hsecond := KernelOperator.expected_synthesis_right_trace_bound μ
    (negativeKernel Λ ρ hΛ hρ.le F) R (fourierBasis (T:=2*π)) (fourierBasis (T:=2*π)) g
    hm hRmeas hC hR hk.1 hk.2.2
  have he (ω : Ω) : (KernelOperator.synthesis (negativeKernel Λ ρ hΛ hρ.le F ω)).comp (R ω)=
      (OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp ((integralOperator F ω).comp (R ω)) := by
    rw [negative_synthesis_eq hΛ hρ.le hF hB hb ω,ContinuousLinearMap.comp_assoc]
  simpa only [he] using And.intro hfirst.1 (And.intro hfirst.2 hsecond.2)

end SHE.NativeRandomKernel
