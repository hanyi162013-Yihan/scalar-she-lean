module

public import SHE.NativeSeparatedAction

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NormalizedKernelSplit
open MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel FiniteHaar
local instance goodNativeSignedKernel_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance goodNativeSignedKernel_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- The good truncation estimate in literal native physical coordinates.
Both the output Q^(1/2) and the signed coefficient-input negative norm
are the actual native Bessel operators, and S_(δ/2) remains on the right. -/
theorem exists_good_native_signed_trace {Ω : Type*} [MeasurableSpace Ω]
    (m U : ℝ) (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
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
      Summable (fun q : HaarNode => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (integralOperator (goodKernel H A R) ω (circleHeatOperator (δ/2) (by positivity)
          (CircleNormalization.push (globalHaarColumn q (DyadicApproximation.realEmbed g)-
            globalHaarColumn q (DyadicApproximation.realEmbed f)))))‖^2) ∧
      (∑' q : HaarNode, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (integralOperator (goodKernel H A R) ω (circleHeatOperator (δ/2) (by positivity)
          (CircleNormalization.push (globalHaarColumn q (DyadicApproximation.realEmbed g)-
            globalHaarColumn q (DyadicApproximation.realEmbed f)))))‖^2) ≤
        J*(R*L)^2*(NativeHeatSpan.clock w)^(ρ-1/2)*(NativeHeatSpan.clock (δ/2))^(-ρ)*
          (1+Real.log (NativeHeatSpan.clock w/NativeHeatSpan.clock (δ/2)))*
          ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le
            (CircleNormalization.push (DyadicApproximation.realEmbed (g-f)))‖^2 := by
  obtain ⟨J,hJ,htrace⟩ := exists_good_signed_trace (Ω:=Ω) m U hm hρ hρhalf
  refine ⟨J,hJ,?_⟩
  intro Λ δ w R L hΛ hδ hw hw1 hδw hR hL H A hH hA B hB hb hheat ω f g hf hg
  have h := htrace Λ δ w R L hΛ hδ hw hw1 hδw hR hL H A hH hA B hB hb hheat ω f g hf hg
  have he (q : HaarNode) := separated_norm_native hΛ hρ.le (show 0 ≤ δ/2 by positivity)
    (goodKernel H A R) ω
    (globalHaarColumn q (DyadicApproximation.realEmbed g)-globalHaarColumn q (DyadicApproximation.realEmbed f))
  simpa only [he,← CircleNormalization.push_bessel_energy hΛ hρ.le] using h

end SHE.NormalizedKernelSplit
