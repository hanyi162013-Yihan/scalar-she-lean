module

public import SHE.NativeSignedHaarProcess
public import SHE.NativeKernelMass

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.SignedKernelEnergy
open Set Filter MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel NativeSignedHaarProcess
open scoped ENNReal
local instance signedKernelEnergy_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance signedKernelEnergy_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance signedKernelEnergy_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance signedKernelEnergy_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance signedKernelEnergy_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance signedKernelEnergy_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance signedKernelEnergy_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance signedKernelEnergy_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance signedKernelEnergy_kernelSecondCountable : SecondCountableTopology KernelSpace := Lp.SecondCountableTopology
local instance signedKernelEnergy_kernelMeasurable : MeasurableSpace KernelSpace := borel KernelSpace
local instance signedKernelEnergy_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual native Hilbert--Schmidt energy with the signed same-Haar
input and the true right heat S_(δ/2). -/
def energy (F : Ω × (HeatCircle × HeatCircle) → ℂ) (Λ ρ δ : ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (c d : CircleHeat.CircleL2) (ω : Ω) : ℝ :=
  ∑' q : FiniteHaar.HaarNode, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
    (integralOperator F ω (circleHeatOperator (δ/2) (by positivity)
      (CircleNormalization.push (FiniteHaar.globalHaarColumn q d-FiniteHaar.globalHaarColumn q c))))‖^2

theorem energy_nonneg (F : Ω × (HeatCircle × HeatCircle) → ℂ) {Λ ρ δ : ℝ}
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (c d : CircleHeat.CircleL2) (ω : Ω) :
    0 ≤ energy F Λ ρ δ hΛ hρ hδ c d ω := tsum_nonneg (fun _ => sq_nonneg _)

theorem energy_measurable {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    {Λ ρ δ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    {c d : Ω → CircleHeat.CircleL2} (hc : Measurable c) (hd : Measurable d) :
    Measurable (fun ω => energy F Λ ρ δ hΛ hρ hδ (c ω) (d ω) ω) := by
  have hK := kernel_measurable hF hB hb
  have hact : Continuous (fun p : KernelSpace × CircleL2 => KernelOperator.synthesis p.1 p.2) :=
    (KernelOperator.synthesis_continuous.comp continuous_fst).clm_apply continuous_snd
  apply Measurable.tsum
  intro q
  have hcol := ((FiniteHaar.measurable_globalHaarColumn q).comp hd).sub
    ((FiniteHaar.measurable_globalHaarColumn q).comp hc)
  have hv := (circleHeatOperator (δ/2) (by positivity)).continuous.measurable.comp
    (CircleNormalization.push.continuous.measurable.comp hcol)
  exact ((OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp
    (hact.measurable.comp (hK.prodMk hv))).norm.pow_const (2:ℕ)

def rightFactor (δ : ℝ) (hδ : 0 ≤ δ) (m U : ℝ) (hm : 0 < m)
    (c d : FiniteHaar.EllipticField m U) : FiniteHaar.HaarInput →L[ℂ] CircleL2 :=
  (circleHeatOperator (δ/2) (by positivity)).comp (signedFactor m U hm c d)

theorem rightFactor_norm_sq {δ m U : ℝ} (hδ : 0 ≤ δ) (hm : 0 < m)
    (c d : FiniteHaar.EllipticField m U) : ‖rightFactor δ hδ m U hm c d‖^2 ≤ 4*U := by
  have hh : ‖circleHeatOperator (δ/2) (by positivity)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ)≤1)
    intro z
    simpa only [one_mul] using circleHeatOperator_norm_le (δ/2) (by positivity) z
  have hn : ‖rightFactor δ hδ m U hm c d‖ ≤ ‖signedFactor m U hm c d‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (signedFactor_norm_sq m U hm c d)

theorem energy_summable_and_bound {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    {Λ ρ δ m U : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hm : 0 < m)
    (c d : FiniteHaar.EllipticField m U) (ω : Ω) :
    Summable (fun q : FiniteHaar.HaarNode => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ
      (integralOperator F ω (circleHeatOperator (δ/2) (by positivity)
        (CircleNormalization.push (FiniteHaar.globalHaarColumn q d.1-FiniteHaar.globalHaarColumn q c.1))))‖^2) ∧
      energy F Λ ρ δ hΛ hρ hδ c.1 d.1 ω ≤ 4*U*‖kernel F ω‖^2 := by
  let R := rightFactor δ hδ m U hm c d
  let Q := OneInputOperator.besselHalf Λ ρ hΛ hρ
  have hs := KernelOperator.synthesis_right_trace (kernel F ω) R (fourierBasis (T:=2*π))
    (fourierBasis (T:=2*π)) NativeHaarKernel.inputBasis
  have hq := HilbertTrace.left_comp ((KernelOperator.synthesis (kernel F ω)).comp R) Q
    NativeHaarKernel.inputBasis hs.1
  have hQ2 : ‖Q‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg Q) (OneInputOperator.besselHalf_opNorm_le Λ ρ hΛ hρ) 2
  have hb := hq.2.trans ((mul_le_mul_of_nonneg_right hQ2 (tsum_nonneg (fun _ => sq_nonneg _))).trans_eq (one_mul _))
  have hb' := hb.trans (hs.2.trans (mul_le_mul_of_nonneg_right (rightFactor_norm_sq hδ hm c d) (sq_nonneg _)))
  simpa only [R,Q,rightFactor,ContinuousLinearMap.comp_apply,signedFactor_basis,integralOperator,energy] using And.intro hq.1 hb'

theorem energy_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    {Λ ρ δ m U : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hm : 0 < m)
    (c d : Ω → FiniteHaar.EllipticField m U) (hc : Measurable c) (hd : Measurable d) :
    Integrable (fun ω => energy F Λ ρ δ hΛ hρ hδ (c ω).1 (d ω).1 ω) μ := by
  apply ((kernel_mass_integrable μ hF hB hb).const_mul (4*U)).mono'
    (energy_measurable hF hB hb hΛ hρ hδ (measurable_subtype_coe.comp hc)
      (measurable_subtype_coe.comp hd)).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖energy F Λ ρ δ hΛ hρ hδ (c ω).1 (d ω).1 ω‖≤4*U*‖kernel F ω‖^2
    rw [Real.norm_of_nonneg (energy_nonneg F hΛ hρ hδ (c ω).1 (d ω).1 ω)]
    exact (energy_summable_and_bound hΛ hρ hδ hm (c ω) (d ω) ω).2)

end SHE.SignedKernelEnergy
