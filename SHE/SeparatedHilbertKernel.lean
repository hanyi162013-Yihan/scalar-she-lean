module

public import SHE.CorrelatedHilbertRelative
public import SHE.HeatedCurrentInput
public import SHE.WeightedMeanOperator
public import SHE.WeightedMeanInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NativeRandomKernel
open scoped ENNReal
local instance separatedHilbertKernel_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance separatedHilbertKernel_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance separatedHilbertKernel_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance separatedHilbertKernel_realSigma : MeasurableSpace RealL2 := borel _
local instance separatedHilbertKernel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance separatedHilbertKernel_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance separatedHilbertKernel_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- An exact right-heat factorization transfers arbitrary dependent
kernel moments to the original random Hilbert input. Only its GLOBAL
Hilbert moments are used, and the quantitative small factor is its
original global current energy. -/
theorem separated_hilbert_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : Ω×(HeatCircle×HeatCircle)→ℂ) (hG : Measurable G)
    {B : ℝ} (hB : 0≤B) (hbound : ∀ ω y x,‖G (ω,(y,x))‖≤B)
    (τ : ℝ) (hτ : 0≤τ)
    (V : Ω→RealL2) (hV : Measurable V) (hiV : Integrable (fun ω=>‖V ω‖^2) μ)
    {mass ρ w A χ CD CG : ℝ} (hmass : 1≤mass) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (hw : 0<w) (hw1 : w≤1) (hA : 0≤A)
    (hχ0 : 0≤χ) (hχ1 : χ<1) (hCD : 0≤CD) (hCG : 0≤CG)
    (p : ℕ) (hp : 0<p) (horder : 1≤(p:ℝ)*(1-χ))
    (hiDh : Integrable (fun ω=>‖V ω‖^((4*(p:ℝ))*(1-χ))) μ)
    (hbDh : (∫ ω,‖V ω‖^((4*(p:ℝ))*(1-χ)) ∂μ)≤CD)
    (hMom : ∀ᵐ z : HeatCircle×HeatCircle ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      (∫ ω,‖G (ω,z)‖^(4*p) ∂μ)≤
        CG*(A*‖ProfileVariance.heatPhysical (8*w) z.1 z.2‖)^(4*p)) :
    (∀ ω,integralOperator F ω (embed (V ω))=
      integralOperator G ω (HeatedCurrentInput.value τ V ω)) →
    let C := GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock w)^(ρ-1/2)*A^2*((CD+CG)/2)^(1/(p:ℝ))
    Integrable (fun ω=>‖OneInputOperator.besselHalf mass ρ hmass hρ.le
      (integralOperator F ω (embed (V ω)))‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
        (integralOperator F ω (embed (V ω)))‖^2 ∂μ)≤
        C*(∫ ω,‖V ω‖^2 ∂μ)^χ := by
  intro hsplit C
  have hv : Measurable (HeatedCurrentInput.value τ V) :=
    embed.continuous.measurable.comp ((heat τ).continuous.measurable.comp hV)
  have hnorm (ω : Ω) : ‖HeatedCurrentInput.value τ V ω‖≤‖V ω‖ :=
    HeatedCurrentInput.value_norm_le τ V ω
  have hi2 : Integrable (fun ω=>‖HeatedCurrentInput.value τ V ω‖^2) μ := by
    apply hiV.mono' (hv.norm.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by rw [Real.norm_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (norm_nonneg _) (hnorm ω) 2)
  have hhigh (ω : Ω) : ‖HeatedCurrentInput.value τ V ω‖^((4*(p:ℝ))*(1-χ))≤
      ‖V ω‖^((4*(p:ℝ))*(1-χ)) :=
    rpow_le_rpow (norm_nonneg _) (hnorm ω) (mul_nonneg (by positivity) (sub_pos.mpr hχ1).le)
  have hih : Integrable (fun ω=>‖HeatedCurrentInput.value τ V ω‖^((4*(p:ℝ))*(1-χ))) μ := by
    apply hiDh.mono' (hv.norm.pow_const _).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by rw [Real.norm_of_nonneg (rpow_nonneg (norm_nonneg _) _)];exact hhigh ω)
  have hbh := (integral_mono hih hiDh hhigh).trans hbDh
  have hh := NativeRandomKernel.correlated_hilbert_input_relative μ hG hB
    hbound (HeatedCurrentInput.value τ V) hv hi2
    hmass hρ hρhalf hw hw1 hA (fun y=>y)
    hχ0 hχ1 hCD hCG p hp horder hih hbh (fun y x=>by
      rw [←NativeHeatSpan.kernel_eq_physical (by positivity : 0<8*w)]
      exact NodeKernelLocal.kernel_norm_pos (NativeHeatSpan.clock_pos (by positivity : 0<8*w)) _) hMom
  refine ⟨by simpa only [hsplit] using hh.1,?_⟩
  have hC : 0≤C := by
    dsimp only [C]
    have htr := GaussianNegativePacket.traceConstant_pos
    have hg := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    have hc := (NativeHeatSpan.clock_pos hw).le
    unfold GaussianNegativePacket.constant
    positivity
  have hlow := Real.rpow_le_rpow
    (integral_nonneg (fun ω=>sq_nonneg ‖HeatedCurrentInput.value τ V ω‖))
    (integral_mono hi2 hiV (fun ω=>pow_le_pow_left₀ (norm_nonneg _) (hnorm ω) 2)) hχ0
  have hb := hh.2
  have hbound' : (∫ ω,‖OneInputOperator.besselHalf mass ρ hmass hρ.le
      (integralOperator F ω (embed (V ω)))‖^2 ∂μ)≤
        C*(∫ ω,‖HeatedCurrentInput.value τ V ω‖^2 ∂μ)^χ := by
    simpa only [hsplit,C] using hb
  exact hbound'.trans (mul_le_mul_of_nonneg_left hlow hC)

end SHE.NativeRandomKernel
