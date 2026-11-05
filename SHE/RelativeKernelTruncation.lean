module

public import SHE.NormalizedAmplitude

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.SignedKernelTruncation
open Set Filter MeasureTheory AddCircle Real StoppedFourier NativeSignedHaarProcess NormalizedKernelSplit
open scoped ENNReal
local instance relativeKernelTruncation_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance relativeKernelTruncation_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance relativeKernelTruncation_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance relativeKernelTruncation_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

/-- The normalized amplitude and both truncation branches are constructed
from the original real kernel. Only its actual relative Gaussian moment
estimate enters; the signed trace estimate itself is a conclusion. -/
theorem exists_expected_from_relative_moments {Ω : Type*} [MeasurableSpace Ω]
    (m U : ℝ) (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ J : ℝ, 0 < J ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Λ δ w D lam ε P C : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 < D → 1 ≤ lam → 0 ≤ C →
      ∀ (r : ℕ), P ≤ ε*(2*r) →
      ∀ (F : Ω × Space → ℂ), Measurable F → (∀ p, (F p).im=0) →
      ∀ (B : ℝ), 0 ≤ B → (∀ ω y x, ‖F (ω,(y,x))‖ ≤ B) →
      (∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
        Integrable (fun ω => ‖F (ω,p)‖^(2*r+2)) μ) →
      (∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
        (∫ ω, ‖F (ω,p)‖^(2*r+2) ∂μ) ≤ C*(heatEnvelope D δ w p)^(2*r+2)) →
      ∀ (c d : Ω → FiniteHaar.EllipticField m U), Measurable c → Measurable d →
      Integrable (fun ω => SignedKernelEnergy.energy F Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω) μ ∧
      (∫ ω, SignedKernelEnergy.energy F Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ) ≤
        2*goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w)*
          (∫ ω, inputEnergy hΛ hρ.le (c ω) (d ω) ∂μ)+
          8*U*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-P) := by
  obtain ⟨J,hJ,htrace⟩ := exists_expected_signed_truncation (Ω:=Ω) m U hm hρ hρhalf
  refine ⟨J,hJ,?_⟩
  intro μ _ Λ δ w D lam ε P C hΛ hδ hw hw1 hδw hD hlam hC r hExponent F hF hreal B hB hb hFn hbound c d hc hd
  let A := normalize (heatEnvelope D δ w) F
  have hA : Measurable A := normalize_measurable (heatEnvelope_continuous hw).measurable hF
  have he : fullKernel (heatEnvelope D δ w) A=F :=
    fullKernel_normalize (heatEnvelope_pos hD hδ hw) hreal
  have hnorm : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
      Integrable (fun ω => |A (ω,p)|^(2*r+2)) μ ∧ (∫ ω, |A (ω,p)|^(2*r+2) ∂μ) ≤ C := by
    filter_upwards [hFn,hbound] with p hp hbp
    exact normalize_moment μ hF p (heatEnvelope_pos hD hδ hw p) (2*r+2) hp hbp
  have hh := htrace μ Λ δ w D lam ε P C hΛ hδ hw hw1 hδw hD.le hlam hC r hExponent A hA B hB
    (by simpa only [he] using hb) (hnorm.mono (fun _ hp => hp.1)) (hnorm.mono (fun _ hp => hp.2)) c d hc hd
  simpa only [he] using hh

end SHE.SignedKernelTruncation
