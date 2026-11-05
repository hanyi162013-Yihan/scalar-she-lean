module

public import SHE.CorrelatedHilbertInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal Topology
local instance correlatedHilbertRelative_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance correlatedHilbertRelative_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance correlatedHilbertRelative_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance correlatedHilbertRelative_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The correlated linear-input estimate consumes the actual relative
kernel moments directly. Deterministic amplitudes may vanish; positive
regularization is removed by a genuine scalar limit. -/
theorem correlated_hilbert_input_relative (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×(HeatCircle×HeatCircle)→ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0≤B) (hb : ∀ ω y x,‖F (ω,(y,x))‖≤B)
    (v : Ω→CircleL2) (hv : Measurable v) (hv2 : Integrable (fun ω=>‖v ω‖^2) μ)
    {Λ ρ t A χ CD CG : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hA : 0≤A)
    (center : HeatCircle→HeatCircle)
    (hχ0 : 0≤χ) (hχ1 : χ<1) (hCD : 0≤CD) (hCG : 0≤CG)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hiDh : Integrable (fun ω=>‖v ω‖^((4*(p:ℝ))*(1-χ))) μ)
    (hbDh : (∫ ω,‖v ω‖^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hheat : ∀ y x,0<‖ProfileVariance.heatPhysical (8*t) (center y) x‖)
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω,‖F (ω,z)‖^(4*p) ∂μ)≤CG*(A*‖ProfileVariance.heatPhysical (8*t) (center z.1) z.2‖)^(4*p)) :
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2 ∂μ)≤
        C*(∫ ω,‖v ω‖^2 ∂μ)^χ := by
  intro C
  have hiF (z : HeatCircle×HeatCircle) : Integrable (fun ω=>‖F (ω,z)‖^(4*p)) μ := by
    apply (integrable_const (B^(4*p))).mono'
      ((hF.comp (measurable_id.prodMk measurable_const)).norm.pow_const _).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb ω z.1 z.2) _)
  have hε (ε : ℝ) (hε : 0<ε) :
      Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2) μ ∧
        (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (integralOperator F ω (v ω))‖^2 ∂μ)≤
          (GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*(A+ε)^2*((CD+CG)/2)^(1/(p:ℝ)))*
            (∫ ω,‖v ω‖^2 ∂μ)^χ := by
    have hAp : 0<A+ε := add_pos_of_nonneg_of_pos hA hε
    apply correlated_hilbert_input_bound μ hF hB hb v hv hv2 hΛ hρ hρhalf ht ht1 hAp
      center hχ0 hχ1 hCD hCG p hp horder hiDh hbDh hheat
    filter_upwards [hMom] with z hz
    let s := (A+ε)*‖ProfileVariance.heatPhysical (8*t) (center z.1) z.2‖
    have hs : 0<s := mul_pos hAp (hheat z.1 z.2)
    have hi : Integrable (fun ω=>(‖F (ω,z)‖/s)^(4*p)) μ := by
      simp_rw [div_pow]
      exact (hiF z).div_const _
    refine ⟨hi,?_⟩
    simp_rw [div_pow]
    rw [integral_div]
    apply (div_le_iff₀ (pow_pos hs _)).mpr
    exact hz.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hA (hheat z.1 z.2).le)
        (mul_le_mul_of_nonneg_right (by linarith : A≤A+ε) (hheat z.1 z.2).le) _) hCG)
  refine ⟨(hε 1 (by norm_num)).1,?_⟩
  have hc : ContinuousAt (fun ε : ℝ=>
      (GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*(A+ε)^2*((CD+CG)/2)^(1/(p:ℝ)))*
        (∫ ω,‖v ω‖^2 ∂μ)^χ) 0 := by fun_prop
  have htend := hc.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hh := ge_of_tendsto htend (by
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    exact (hε ε hεpos).2)
  simpa only [add_zero,C] using hh

end SHE.NativeRandomKernel
