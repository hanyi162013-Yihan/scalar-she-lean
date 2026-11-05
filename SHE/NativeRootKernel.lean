module

public import SHE.NativeRootPartition

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRootPartition
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier NativeRandomKernel
open scoped BigOperators ENNReal
local instance nativeRootKernel_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeRootKernel_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeRootKernel_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance nativeRootKernel_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeRootKernel_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeRootKernel_kernelSecondCountable : SecondCountableTopology KernelSpace :=
  Lp.SecondCountableTopology
local instance nativeRootKernel_kernelMeasurable : MeasurableSpace KernelSpace := borel KernelSpace
local instance nativeRootKernel_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩

variable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]

theorem column_eq_sum (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ha : ∀ i, Measurable (a i))
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) (p : Ω × HeatCircle) :
    column F p=∑ i, column (component t a F i) p := by
  classical
  have hall : ∀ᵐ x : HeatCircle ∂haarAddCircle, ∀ i : I,
      column (component t a F i) p x=component t a F i (p.1,(p.2,x)) :=
    ae_all_iff.mpr (fun i => column_ae (component_measurable t a ht ha hF i)
      (component_bound t a ht hB hb i) p.1 p.2)
  apply Lp.ext
  filter_upwards [column_ae hF hb p.1 p.2,Lp.coeFn_finsetSum Finset.univ
    (fun i => column (component t a F i) p),hall] with x hf hs hx
  change column F p x=(∑ i, column (component t a F i) p) x
  rw [hf,hs,Finset.sum_apply]
  simp_rw [hx]
  exact (component_sum t a ht F (p.1,(p.2,x))).symm

/-- The finite root decomposition holds in the actual Hilbert-valued
negative-output kernel space, with every original sign preserved. -/
theorem negativeKernel_eq_sum (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ha : ∀ i, Measurable (a i))
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ω : Ω) :
    negativeKernel Λ ρ hΛ hρ F ω=∑ i, negativeKernel Λ ρ hΛ hρ (component t a F i) ω := by
  classical
  have hall : ∀ᵐ y : HeatCircle ∂haarAddCircle, ∀ i : I,
      negativeKernel Λ ρ hΛ hρ (component t a F i) ω y=
        negativeColumn Λ ρ hΛ hρ (component t a F i) (ω,y) :=
    ae_all_iff.mpr (fun i => negativeKernel_ae hΛ hρ (component_measurable t a ht ha hF i) hB
      (component_bound t a ht hB hb i) ω)
  apply Lp.ext
  filter_upwards [negativeKernel_ae hΛ hρ hF hB hb ω,Lp.coeFn_finsetSum Finset.univ
    (fun i => negativeKernel Λ ρ hΛ hρ (component t a F i) ω),hall] with y hf hs hy
  change negativeKernel Λ ρ hΛ hρ F ω y=(∑ i, negativeKernel Λ ρ hΛ hρ (component t a F i) ω) y
  rw [hf,hs,Finset.sum_apply]
  simp_rw [hy]
  change OneInputOperator.besselHalf Λ ρ hΛ hρ (column F (ω,y))=
    ∑ i, OneInputOperator.besselHalf Λ ρ hΛ hρ (column (component t a F i) (ω,y))
  rw [column_eq_sum t a ht ha hF hB hb (ω,y),map_sum]

/-- True expected negative-output kernel energy for an arbitrary finite
sum of original-root RMS envelopes. Each root keeps its own age and
location; no age-comparability premise is introduced. -/
theorem expected_negativeKernel_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1) (ha : ∀ i, Measurable (a i))
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B K Λ ρ : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (hK : 0 ≤ K) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hsharp : ∀ y x, ProfileL2.normTwo μ (fun ω => ‖F (ω,(y,x))‖) ≤ K*total t a (y,x)) :
    Integrable (fun ω => ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ ω, ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ) ≤
        (Fintype.card I:ℝ)*∑ i, GaussianNegativePacket.constant ρ*
          (NativeHeatSpan.clock (t i))^(ρ-1/2)*K^2 ∧
      (∫ ω, ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ) ≤
        (Fintype.card I:ℝ)*∑ i, GaussianNegativePacket.traceConstant*Λ^(-ρ)*
          (NativeHeatSpan.clock (t i))^(-(1/2:ℝ))*K^2 := by
  classical
  have hpart (i : I) := NativeRandomKernel.expected_negativeKernel_bound μ
    (component_measurable t a ht ha hF i) hB (component_bound t a ht hB hb i)
    hΛ hρ hρhalf (ht i) (ht1 i) hK (a i) (component_rms_bound μ t a ht hF hb hsharp i)
  have hdom (ω : Ω) : ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ≤
      (Fintype.card I:ℝ)*∑ i, ‖negativeKernel Λ ρ hΛ hρ.le (component t a F i) ω‖^2 := by
    rw [negativeKernel_eq_sum t a ht ha hF hB hb hΛ hρ.le ω]
    simpa only [Finset.card_univ] using norm_sq_finset_sum_le Finset.univ
      (fun i => negativeKernel Λ ρ hΛ hρ.le (component t a F i) ω)
  have hsum : Integrable (fun ω => ∑ i, ‖negativeKernel Λ ρ hΛ hρ.le (component t a F i) ω‖^2) μ :=
    integrable_finsetSum _ (fun i _ => (hpart i).1)
  have hInt : Integrable (fun ω => ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ := by
    apply (hsum.const_mul (Fintype.card I:ℝ)).mono'
      ((negativeKernel_measurable hΛ hρ.le hF hB hb).norm.pow_const (2:ℕ)).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hdom ω)
  have hbnd : (∫ ω, ‖negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ) ≤
      (Fintype.card I:ℝ)*∑ i, ∫ ω, ‖negativeKernel Λ ρ hΛ hρ.le (component t a F i) ω‖^2 ∂μ := by
    calc
      _ ≤ ∫ ω, (Fintype.card I:ℝ)*∑ i, ‖negativeKernel Λ ρ hΛ hρ.le (component t a F i) ω‖^2 ∂μ :=
        integral_mono hInt (hsum.const_mul _) hdom
      _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hpart i).1)]
  refine ⟨hInt,hbnd.trans ?_,hbnd.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hpart i).2.1)) (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hpart i).2.2)) (Nat.cast_nonneg _)

/-- The actual signed integral operator with finitely many original-root
RMS envelopes has the required negative-output Hilbert--Schmidt bound,
including an arbitrary bounded noise right factor sharing its randomness. -/
theorem expected_negative_right_trace
    {G N : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Countable N] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1) (ha : ∀ i, Measurable (a i))
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B K Λ ρ C : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (hK : 0 ≤ K) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hsharp : ∀ y x, ProfileL2.normTwo μ (fun ω => ‖F (ω,(y,x))‖) ≤ K*total t a (y,x))
    (R : Ω → G →L[ℂ] CircleL2) (g : HilbertBasis N ℂ G)
    (hC : 0 ≤ C) (hR : ∀ ω, ‖R ω‖^2 ≤ C)
    (hRmeas : ∀ n, Measurable (fun ω => R ω (g n))) :
    Integrable (fun ω => ∑' n, ‖((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp
      ((integralOperator F ω).comp (R ω))) (g n)‖^2) μ ∧
      (∫ ω, ∑' n, ‖((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp
        ((integralOperator F ω).comp (R ω))) (g n)‖^2 ∂μ) ≤
        C*((Fintype.card I:ℝ)*∑ i, GaussianNegativePacket.constant ρ*
          (NativeHeatSpan.clock (t i))^(ρ-1/2)*K^2) ∧
      (∫ ω, ∑' n, ‖((OneInputOperator.besselHalf Λ ρ hΛ hρ.le).comp
        ((integralOperator F ω).comp (R ω))) (g n)‖^2 ∂μ) ≤
        C*((Fintype.card I:ℝ)*∑ i, GaussianNegativePacket.traceConstant*Λ^(-ρ)*
          (NativeHeatSpan.clock (t i))^(-(1/2:ℝ))*K^2) := by
  have hk := expected_negativeKernel_bound μ t a ht ht1 ha hF hB hb hK hΛ hρ hρhalf hsharp
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

end SHE.NativeRootPartition
