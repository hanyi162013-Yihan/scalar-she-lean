module

public import SHE.RelativeKernelTruncation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.SignedKernelTruncation
open Set Filter MeasureTheory AddCircle Real StoppedFourier NativeSignedHaarProcess NormalizedKernelSplit
open scoped ENNReal Topology
local instance relativeKernelTruncationZero_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance relativeKernelTruncationZero_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance relativeKernelTruncationZero_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance relativeKernelTruncationZero_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

theorem goodCost_amplitude_homogeneous (J ρ δ w R D : ℝ) :
    goodCost J ρ δ w R (heatAmplitude D δ w)=D^2*goodCost J ρ δ w R (heatAmplitude 1 δ w) := by
  unfold goodCost heatAmplitude
  ring

/-- Vanishing deterministic clips need no separate nondegeneracy input.
The true kernel is normalized against D+ε and the proved estimate is
passed to ε↓0, so the final theorem includes D=0 automatically. -/
theorem exists_expected_relative_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (m U : ℝ) (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ J : ℝ, 0 < J ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Λ δ w D lam ε P C : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ D → 1 ≤ lam → 0 ≤ C →
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
  obtain ⟨J,hJ,htrace⟩ := exists_expected_from_relative_moments (Ω:=Ω) m U hm hρ hρhalf
  refine ⟨J,hJ,?_⟩
  intro μ _ Λ δ w D lam ε P C hΛ hδ hw hw1 hδw hD hlam hC r hExponent F hF hreal B hB hb hFn hbound c d hc hd
  let M : ℝ := 2*goodCost J ρ δ w (lam^ε) (heatAmplitude 1 δ w)*
    (∫ ω,inputEnergy hΛ hρ.le (c ω) (d ω) ∂μ)+8*U*C*heatMassConstant*δ^(-1:ℝ)*lam^(-P)
  have hid (a : ℝ) :
      2*goodCost J ρ δ w (lam^ε) (heatAmplitude a δ w)*(∫ ω,inputEnergy hΛ hρ.le (c ω) (d ω) ∂μ)+
        8*U*C*heatMassConstant*a^2*δ^(-1:ℝ)*lam^(-P)=M*a^2 := by
    rw [goodCost_amplitude_homogeneous]
    dsimp only [M]
    ring
  have hs (a : ℝ) (ha : 0 < a) (hDa : D ≤ a) :
      (∫ ω, SignedKernelEnergy.energy F Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ) ≤ M*a^2 := by
    have henvelope (p : Space) : 0 ≤ heatEnvelope D δ w p ∧ heatEnvelope D δ w p ≤ heatEnvelope a δ w p := by
      unfold heatEnvelope heatAmplitude
      constructor
      · positivity
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDa (Real.rpow_nonneg hδ.le _))
            (Real.rpow_nonneg hw.le _)) (norm_nonneg _)
    have hb' : ∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
        (∫ ω, ‖F (ω,p)‖^(2*r+2) ∂μ) ≤ C*(heatEnvelope a δ w p)^(2*r+2) := by
      filter_upwards [hbound] with p hp
      exact hp.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (henvelope p).1 (henvelope p).2 _) hC)
    have hh := (htrace μ Λ δ w a lam ε P C hΛ hδ hw hw1 hδw ha hlam hC r hExponent F hF hreal
      B hB hb hFn hb' c d hc hd).2
    rwa [hid a] at hh
  refine ⟨SignedKernelEnergy.energy_integrable μ hF hB hb hΛ hρ.le hδ.le hm c d hc hd,?_⟩
  rw [hid D]
  have ht : Tendsto (fun e : ℝ => M*(D+e)^2) (𝓝[>] (0:ℝ)) (𝓝 (M*D^2)) := by
    have hc0 : ContinuousAt (fun e : ℝ => M*(D+e)^2) 0 := by fun_prop
    simpa only [add_zero] using hc0.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with e he
  exact hs (D+e) (by have he' : 0 < e := he; linarith) (by have he' : 0 < e := he; linarith)

end SHE.SignedKernelTruncation
