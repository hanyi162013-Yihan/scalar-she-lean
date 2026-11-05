module

public import SHE.NativeHaarKernel
public import SHE.HaarDamping

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeSignedHaarProcess
open MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeSignedHaarProcess_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeSignedHaarProcess_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeSignedHaarProcess_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeSignedHaarProcess_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeSignedHaarProcess_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeSignedHaarProcess_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeSignedHaarProcess_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩

def realCoefficient {m U : ℝ} (c : FiniteHaar.EllipticField m U) : DyadicApproximation.RealL2 :=
  DyadicApproximation.realPart c.1

theorem realEmbed_realCoefficient {m U : ℝ} (c : FiniteHaar.EllipticField m U) :
    DyadicApproximation.realEmbed (realCoefficient c)=c.1 := by
  apply Lp.ext
  filter_upwards [DyadicApproximation.realEmbed_ae (realCoefficient c),Complex.reCLM.coeFn_compLp c.1,c.2.1]
    with y he hr hi
  rw [he]
  change realCoefficient c y=(c.1 y).re at hr
  rw [hr]
  exact Complex.ext (by simp) (by simpa using hi.symm)

def signedFactor (m U : ℝ) (hm : 0 < m) (c d : FiniteHaar.EllipticField m U) :
    FiniteHaar.HaarInput →L[ℂ] CircleL2 := NativeHaarKernel.factor m U hm d-NativeHaarKernel.factor m U hm c

theorem signedFactor_basis (m U : ℝ) (hm : 0 < m) (c d : FiniteHaar.EllipticField m U)
    (q : FiniteHaar.HaarNode) : signedFactor m U hm c d (NativeHaarKernel.inputBasis q)=
      CircleNormalization.push (FiniteHaar.globalHaarColumn q d.1-FiniteHaar.globalHaarColumn q c.1) := by
  simp only [signedFactor,ContinuousLinearMap.sub_apply,NativeHaarKernel.factor_basis,map_sub]

theorem signedFactor_norm_sq (m U : ℝ) (hm : 0 < m) (c d : FiniteHaar.EllipticField m U) :
    ‖signedFactor m U hm c d‖^2 ≤ 4*U := by
  have hc := NativeHaarKernel.factor_norm_sq_le m U hm c
  have hd := NativeHaarKernel.factor_norm_sq_le m U hm d
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_sub_le (NativeHaarKernel.factor m U hm d) (NativeHaarKernel.factor m U hm c)) 2
  change ‖signedFactor m U hm c d‖^2 ≤ _ at h
  nlinarith [sq_nonneg (‖NativeHaarKernel.factor m U hm d‖-‖NativeHaarKernel.factor m U hm c‖)]

theorem signedFactor_column_measurable {Ω : Type*} [MeasurableSpace Ω]
    (m U : ℝ) (hm : 0 < m) (c d : Ω → FiniteHaar.EllipticField m U)
    (hc : Measurable c) (hd : Measurable d) (q : FiniteHaar.HaarNode) :
    Measurable (fun ω => signedFactor m U hm (c ω) (d ω) (NativeHaarKernel.inputBasis q)) :=
  (NativeHaarKernel.factor_column_measurable m U hm d hd q).sub
    (NativeHaarKernel.factor_column_measurable m U hm c hc q)

def inputEnergy {m U Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (c d : FiniteHaar.EllipticField m U) : ℝ :=
  ‖OneInputOperator.besselHalf Λ ρ hΛ hρ (CircleNormalization.push (d.1-c.1))‖^2

theorem inputEnergy_bound {m U Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (c d : FiniteHaar.EllipticField m U) : inputEnergy hΛ hρ c d ≤ (U-m)^2 := by
  have hh := (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ (CircleNormalization.push (d.1-c.1))).trans_eq
    (CircleNormalization.push.norm_map (d.1-c.1))
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans
    (pow_le_pow_left₀ (norm_nonneg _) (FiniteHaar.elliptic_difference_norm_le d.1 c.1 d.2.1 c.2.1 d.2.2 c.2.2) 2)

theorem inputEnergy_measurable {Ω : Type*} [MeasurableSpace Ω] {m U Λ ρ : ℝ}
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (c d : Ω → FiniteHaar.EllipticField m U)
    (hc : Measurable c) (hd : Measurable d) : Measurable (fun ω => inputEnergy hΛ hρ (c ω) (d ω)) := by
  exact (((OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp
    (CircleNormalization.push.continuous.measurable.comp
      ((measurable_subtype_coe.comp hd).sub (measurable_subtype_coe.comp hc)))).norm.pow_const (2:ℕ))

theorem inputEnergy_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m U Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (c d : Ω → FiniteHaar.EllipticField m U)
    (hc : Measurable c) (hd : Measurable d) : Integrable (fun ω => inputEnergy hΛ hρ (c ω) (d ω)) μ := by
  apply (integrable_const ((U-m)^2)).mono' (inputEnergy_measurable hΛ hρ c d hc hd).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_of_nonneg (show 0 ≤ inputEnergy hΛ hρ (c ω) (d ω) from sq_nonneg _)]
    exact inputEnergy_bound hΛ hρ (c ω) (d ω))

end SHE.NativeSignedHaarProcess
