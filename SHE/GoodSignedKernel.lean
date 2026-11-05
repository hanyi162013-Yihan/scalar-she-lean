module

public import SHE.NormalizedKernelSplit
public import SHE.HaarScaledTaylor

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open Set Filter MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel FiniteHaar
open scoped ENNReal
local instance goodSignedKernel_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance goodSignedKernel_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The genuinely truncated normalized kernel, before its true right
heat factor, satisfies the pathwise Gaussian envelope required by the
signed Haar transport theorem. -/
def goodDominatedKernel {H : Space → ℝ} {A : Ω × Space → ℝ}
    (hH : Measurable H) (hA : Measurable A) {B R L w : ℝ}
    (hB : 0 ≤ B) (hb : ∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B)
    (hR : 0 ≤ R) (hw : 0 < w) (ω : Ω)
    (hheat : ∀ y x, |H (y,x)| ≤ L*‖ProfileVariance.heatPhysical (8*w) y x‖) :
    HeatDominatedKernel (NativeHeatSpan.clock (8*w)) (R*L) (NativeHeatSpan.clock_pos (by positivity)) :=
  dominatedKernel (by positivity) (goodKernel_measurable hH hA R) hB (goodKernel_bound hB hb R) ω
    (fun y x => (goodKernel_envelope hR (ω,(y,x))).trans
      ((mul_le_mul_of_nonneg_left (hheat y x) hR).trans_eq (by ring)))

/-- The good branch retains the actual signed negative-input coefficient
difference and the inner S_(δ/2). The cutoff cost is precisely its squared
amplitude R²; no negative-input smallness is inferred from a bounded
right-factor estimate. Native ages are converted explicitly by `clock`. -/
theorem exists_good_signed_trace (m U : ℝ) (hm : 0 < m)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ J : ℝ, 0 < J ∧ ∀ (Λ δ w R L : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ R → 0 ≤ L →
      ∀ (H : Space → ℝ) (A : Ω × Space → ℝ) (hH : Measurable H) (hA : Measurable A)
      (B : ℝ), 0 ≤ B → (∀ ω y x, ‖fullKernel H A (ω,(y,x))‖ ≤ B) →
      (∀ y x, |H (y,x)| ≤ L*‖ProfileVariance.heatPhysical (8*w) y x‖) →
      ∀ (ω : Ω) (f g : DyadicApproximation.RealL2),
      (∀ᵐ y ∂haarAddCircle,m ≤ (DyadicApproximation.realEmbed f y).re ∧
        (DyadicApproximation.realEmbed f y).re ≤ U) →
      (∀ᵐ y ∂haarAddCircle,m ≤ (DyadicApproximation.realEmbed g y).re ∧
        (DyadicApproximation.realEmbed g y).re ≤ U) →
      Summable (fun q : HaarNode => ‖separatedHeat Λ ρ (NativeHeatSpan.clock (δ/2)) hΛ hρ.le
        (unitOperator (goodKernel H A R) ω)
        (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))‖^2) ∧
      (∑' q : HaarNode,‖separatedHeat Λ ρ (NativeHeatSpan.clock (δ/2)) hΛ hρ.le
        (unitOperator (goodKernel H A R) ω)
        (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))‖^2) ≤
        J*(R*L)^2*(NativeHeatSpan.clock w)^(ρ-1/2)*(NativeHeatSpan.clock (δ/2))^(-ρ)*
          (1+Real.log (NativeHeatSpan.clock w/NativeHeatSpan.clock (δ/2)))*
          StepInput.negativeEnergy 1 Λ ρ (DyadicApproximation.realEmbed (g-f)) := by
  obtain ⟨J,hJ,htrace⟩ := exists_global_scaled_signed_trace m U hm hρ hρhalf (by norm_num : (0:ℝ)<8)
  refine ⟨J,hJ,?_⟩
  intro Λ δ w R L hΛ hδ hw hw1 hδw hR hL H A hH hA B hB hb hheat ω f g hf hg
  have hden : 1 ≤ 4*π^2 := by nlinarith [Real.two_le_pi]
  have hcw : 0 < NativeHeatSpan.clock w := NativeHeatSpan.clock_pos hw
  have hcδ : 0 < NativeHeatSpan.clock (δ/2) := NativeHeatSpan.clock_pos (by positivity)
  have hcw1 : NativeHeatSpan.clock w ≤ 1 :=
    (div_le_one (by positivity : 0 < 4*π^2)).mpr (hw1.trans hden)
  have hcδw : NativeHeatSpan.clock (δ/2) ≤ NativeHeatSpan.clock w :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hclock : NativeHeatSpan.clock (8*w)=8*NativeHeatSpan.clock w := by
    unfold NativeHeatSpan.clock
    ring
  let D0 := goodDominatedKernel hH hA hB hb hR hw ω hheat
  let D : HeatDominatedKernel (8*NativeHeatSpan.clock w) (R*L) (by positivity) := {
    operator := D0.operator
    kernel := D0.kernel
    measurable_kernel := D0.measurable_kernel
    kernel_bound := by
      intro x y
      simpa only [hclock] using D0.kernel_bound x y
    representation := D0.representation }
  exact htrace Λ (NativeHeatSpan.clock (δ/2)) (NativeHeatSpan.clock w) (R*L) hΛ hcδ hcw hcw1 hcδw
    (mul_nonneg hR hL) D f g hf hg

end SHE.NormalizedKernelSplit
