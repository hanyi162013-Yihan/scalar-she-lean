module

public import SHE.SignedKernelEnergy
public import SHE.GoodNativeSignedKernel
public import SHE.BadHeatKernelTail
public import SHE.NormalizedKernelAlgebra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.SignedKernelTruncation
open Set Filter MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel NativeSignedHaarProcess
  NormalizedKernelSplit
open scoped ENNReal
local instance signedKernelTruncation_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance signedKernelTruncation_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance signedKernelTruncation_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance signedKernelTruncation_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance signedKernelTruncation_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

def goodCost (J ρ δ w R L : ℝ) : ℝ :=
  J*(R*L)^2*(NativeHeatSpan.clock w)^(ρ-1/2)*(NativeHeatSpan.clock (δ/2))^(-ρ)*
    (1+Real.log (NativeHeatSpan.clock w/NativeHeatSpan.clock (δ/2)))

/-- The full native signed-noise row is truncated before its actual
right heat and same-Haar factor difference. The good term retains the
genuine signed negative-input energy; the bad term is an arbitrary
polynomial tail from a sufficiently high fixed normalized-amplitude
moment. All random factors may be dependent, and all actual column
measurability and energy integrability are proved. -/
theorem exists_expected_signed_truncation {Ω : Type*} [MeasurableSpace Ω]
    (m U : ℝ) (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ J : ℝ, 0 < J ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Λ δ w D lam ε P C : ℝ) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ D → 1 ≤ lam → 0 ≤ C →
      ∀ (r : ℕ), P ≤ ε*(2*r) →
      ∀ (A : Ω × Space → ℝ), Measurable A →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ ω y x, ‖fullKernel (heatEnvelope D δ w) A (ω,(y,x))‖ ≤ B) →
      (∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
        Integrable (fun ω => |A (ω,p)|^(2*r+2)) μ) →
      (∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
        (∫ ω, |A (ω,p)|^(2*r+2) ∂μ) ≤ C) →
      ∀ (c d : Ω → FiniteHaar.EllipticField m U), Measurable c → Measurable d →
      Integrable (fun ω => SignedKernelEnergy.energy (fullKernel (heatEnvelope D δ w) A)
        Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω) μ ∧
      (∫ ω, SignedKernelEnergy.energy (fullKernel (heatEnvelope D δ w) A)
        Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ) ≤
        2*goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w)*
          (∫ ω, inputEnergy hΛ hρ.le (c ω) (d ω) ∂μ)+
          8*U*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-P) := by
  obtain ⟨J,hJ,hgood⟩ := exists_good_native_signed_trace (Ω:=Ω) m U hm hρ hρhalf
  refine ⟨J,hJ,?_⟩
  intro μ _ Λ δ w D lam ε P C hΛ hδ hw hw1 hδw hD hlam hC r hExponent A hA B hB hb hAn hbound c d hc hd
  have hH := (heatEnvelope_continuous (D:=D) (δ:=δ) hw).measurable
  have hfull := fullKernel_measurable hH hA
  have hgoodMeas := goodKernel_measurable hH hA (lam^ε)
  have hbadMeas := badKernel_measurable hH hA (lam^ε)
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hR : 0 ≤ lam^ε := (Real.rpow_pos_of_pos hlam0 ε).le
  have hL : 0 ≤ heatAmplitude D δ w := by unfold heatAmplitude; positivity
  have hheat (y x : HeatCircle) : |heatEnvelope D δ w (y,x)| ≤
      heatAmplitude D δ w*‖ProfileVariance.heatPhysical (8*w) y x‖ := by
    exact le_of_eq (abs_of_nonneg (mul_nonneg hL (norm_nonneg _)))
  have hg (ω : Ω) :
      Summable (fun q : FiniteHaar.HaarNode => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le
        (integralOperator (goodKernel (heatEnvelope D δ w) A (lam^ε)) ω (circleHeatOperator (δ/2) (by positivity)
          (CircleNormalization.push (FiniteHaar.globalHaarColumn q (d ω).1-FiniteHaar.globalHaarColumn q (c ω).1))))‖^2) ∧
      SignedKernelEnergy.energy (goodKernel (heatEnvelope D δ w) A (lam^ε)) Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ≤
        goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w)*inputEnergy hΛ hρ.le (c ω) (d ω) := by
    have hh := hgood Λ δ w (lam^ε) (heatAmplitude D δ w) hΛ hδ hw hw1 hδw hR hL
      (heatEnvelope D δ w) A hH hA B hB hb hheat ω (realCoefficient (c ω)) (realCoefficient (d ω))
      (by simpa only [realEmbed_realCoefficient] using (c ω).2.2)
      (by simpa only [realEmbed_realCoefficient] using (d ω).2.2)
    simpa only [realEmbed_realCoefficient,map_sub,SignedKernelEnergy.energy,goodCost,inputEnergy] using hh
  have hU : 0 ≤ U := by
    obtain ⟨ω,_⟩ := (ae_of_all μ (fun _ : Ω => True.intro)).exists
    exact FiniteHaar.elliptic_upper_nonneg (c ω).1 m U hm (c ω).2.2
  have hbad := expected_bad_heat_trace_polynomial μ hA hδ hw hw1 hB hb hC r hlam hExponent hAn hbound hΛ hρ.le
    (fun ω => signedFactor m U hm (c ω) (d ω)) NativeHaarKernel.inputBasis
    (by positivity : 0 ≤ 4*U) (fun ω => signedFactor_norm_sq m U hm (c ω) (d ω))
    (signedFactor_column_measurable m U hm c d hc hd)
  have hbInt : Integrable (fun ω => SignedKernelEnergy.energy (badKernel (heatEnvelope D δ w) A (lam^ε))
      Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω) μ := by
    simpa only [signedFactor_basis,SignedKernelEnergy.energy] using hbad.1
  have hbBound : (∫ ω, SignedKernelEnergy.energy (badKernel (heatEnvelope D δ w) A (lam^ε))
      Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ) ≤
      (4*U)*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-P) := by
    simpa only [signedFactor_basis,SignedKernelEnergy.energy] using hbad.2
  have hfInt := SignedKernelEnergy.energy_integrable μ hfull hB hb hΛ hρ.le hδ.le hm c d hc hd
  have hEInt := inputEnergy_integrable μ hΛ hρ.le c d hc hd
  have hp (ω : Ω) : SignedKernelEnergy.energy (fullKernel (heatEnvelope D δ w) A) Λ ρ δ hΛ hρ.le hδ.le
      (c ω).1 (d ω).1 ω ≤
      (2*goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w))*inputEnergy hΛ hρ.le (c ω) (d ω)+
        2*SignedKernelEnergy.energy (badKernel (heatEnvelope D δ w) A (lam^ε)) Λ ρ δ hΛ hρ.le hδ.le
          (c ω).1 (d ω).1 ω := by
    have hbs := (SignedKernelEnergy.energy_summable_and_bound (F:=badKernel (heatEnvelope D δ w) A (lam^ε))
      hΛ hρ.le hδ.le hm (c ω) (d ω) ω).1
    have hh := (full_trace_le_good_bad hH hA hB hb (lam^ε) ω (OneInputOperator.besselHalf Λ ρ hΛ hρ.le)
      (fun q => circleHeatOperator (δ/2) (by positivity)
        (CircleNormalization.push (FiniteHaar.globalHaarColumn q (d ω).1-FiniteHaar.globalHaarColumn q (c ω).1)))
      (hg ω).1 hbs).2
    change SignedKernelEnergy.energy (fullKernel (heatEnvelope D δ w) A) Λ ρ δ hΛ hρ.le hδ.le
      (c ω).1 (d ω).1 ω ≤ 2*SignedKernelEnergy.energy (goodKernel (heatEnvelope D δ w) A (lam^ε))
        Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω+
          2*SignedKernelEnergy.energy (badKernel (heatEnvelope D δ w) A (lam^ε))
            Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω at hh
    nlinarith [(hg ω).2]
  refine ⟨hfInt,?_⟩
  calc
    _ ≤ ∫ ω, (2*goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w))*inputEnergy hΛ hρ.le (c ω) (d ω)+
        2*SignedKernelEnergy.energy (badKernel (heatEnvelope D δ w) A (lam^ε))
          Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ :=
      integral_mono hfInt ((hEInt.const_mul _).add (hbInt.const_mul 2)) hp
    _ = (2*goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w))*(∫ ω,inputEnergy hΛ hρ.le (c ω) (d ω) ∂μ)+
        2*(∫ ω,SignedKernelEnergy.energy (badKernel (heatEnvelope D δ w) A (lam^ε))
          Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ) := by
      rw [integral_add (hEInt.const_mul _) (hbInt.const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by nlinarith [hbBound]

end SHE.SignedKernelTruncation
