module

public import SHE.RandomRowEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RandomRowEnergy
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real CircleHeat HeatMarkov NegativeNash
open scoped BigOperators ENNReal
local instance randomNegativeRows_periodPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance randomNegativeRows_exponentFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance randomNegativeRows_measurableSpace : MeasurableSpace CircleL2 := borel CircleL2
local instance randomNegativeRows_borelSpace : BorelSpace CircleL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Expected negative-output energy from the actual RMS heat envelope.
The coarse uniform bound supplies only Borel/Fubini applicability. All
quantitative constants use the sharp RMS envelope, so arbitrary dependence
between the random row and all coefficient/score variables is retained. -/
theorem expected_dominated_negative
    {F : Ω × UnitAddCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B)
    {Λ ρ t K : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 ≤ K) (a : UnitAddCircle)
    (hsharp : ∀ x, rms μ F x ≤ K*‖kernel (8*t) (by positivity) (x-a)‖) :
    Integrable (fun ω => energy Λ ρ (row F ω)) μ ∧
      (∫ ω, energy Λ ρ (row F ω) ∂μ) ≤ GaussianNegativePacket.constant ρ*t^(ρ-1/2)*K^2 ∧
      (∫ ω, energy Λ ρ (row F ω) ∂μ) ≤
        GaussianNegativePacket.traceConstant*Λ^(-ρ)*t^(-(1/2:ℝ))*K^2 := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hG : 0 ≤ HeatTrace.fractionalGaussianIntegral ρ := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
  let E : Ω → ℝ := fun ω => energy Λ ρ (row F ω)
  have hnonneg (ω : Ω) : 0 ≤ E ω := by
    unfold E energy
    exact tsum_nonneg (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  have hEc : Continuous (energy Λ ρ : CircleL2 → ℝ) := by
    have he : (energy Λ ρ : CircleL2 → ℝ)=StepInput.negativeEnergy 1 Λ ρ :=
      funext (energy_eq_negativeEnergy Λ ρ hΛ0)
    rw [he]
    exact FiniteHaar.continuous_negativeEnergy hΛ0 hρ.le
  have hEm : Measurable E := hEc.measurable.comp (row_measurable hF hb)
  obtain ⟨hi2,he2⟩ := expected_norm_sq μ hF hB hb
  obtain ⟨hi1,he1⟩ := expected_normOne_sq μ hF hB hb
  have hdom : ∀ᵐ x ∂haarAddCircle, ‖rmsRow μ F x‖ ≤ K*‖kernel (8*t) (by positivity) (x-a)‖ := by
    filter_upwards [rmsRow_ae μ hF hB hb] with x hx
    rw [hx,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (rms_nonneg μ F x)]
    exact hsharp x
  have hn := GaussianNegativePacket.dominated_norms ht ht1 hK a (rmsRow μ F) hdom
  have h1 : (∫ ω, normOne (row F ω)^2 ∂μ) ≤ K^2 := he1.trans hn.2
  have h2 : (∫ ω, ‖row F ω‖^2 ∂μ) ≤ GaussianNegativePacket.traceConstant*t^(-(1/2:ℝ))*K^2 :=
    he2.le.trans hn.1
  let A : ℝ := (1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp (ω : Ω) : E ω ≤ A*normOne (row F ω)^2+t^ρ*‖row F ω‖^2 :=
    energy_cutoff hΛ hρ hρhalf ht ht1 (row F ω)
  have hiDom := (hi1.const_mul A).add (hi2.const_mul (t^ρ))
  have hi : Integrable E μ := by
    apply hiDom.mono' hEm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      change ‖E ω‖ ≤ _
      rw [Real.norm_of_nonneg (hnonneg ω)]
      exact hp ω)
  have hf : (∫ ω,E ω ∂μ) ≤ GaussianNegativePacket.constant ρ*t^(ρ-1/2)*K^2 := by
    calc
      _ ≤ ∫ ω,A*normOne (row F ω)^2+t^ρ*‖row F ω‖^2 ∂μ := integral_mono hi hiDom hp
      _ = A*(∫ ω,normOne (row F ω)^2 ∂μ)+t^ρ*(∫ ω,‖row F ω‖^2 ∂μ) := by
        rw [integral_add (hi1.const_mul A) (hi2.const_mul (t^ρ)),integral_const_mul,integral_const_mul]
      _ ≤ A*K^2+t^ρ*(GaussianNegativePacket.traceConstant*t^(-(1/2:ℝ))*K^2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hA)
          (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht.le _))
      _ = _ := by
        rw [show t^ρ*(GaussianNegativePacket.traceConstant*t^(-(1/2:ℝ))*K^2)=
          GaussianNegativePacket.traceConstant*(t^ρ*t^(-(1/2:ℝ)))*K^2 by ring,
          ← Real.rpow_add ht]
        unfold A GaussianNegativePacket.constant
        ring
  have hm (ω : Ω) : E ω ≤ Λ^(-ρ)*‖row F ω‖^2 := by
    change energy Λ ρ (row F ω) ≤ _
    rw [energy_eq_negativeEnergy Λ ρ hΛ0]
    exact FiniteHaar.negativeEnergy_le_L2 (κ:=1) hΛ0 hρ.le (row F ω)
  have hmass : (∫ ω,E ω ∂μ) ≤ GaussianNegativePacket.traceConstant*Λ^(-ρ)*t^(-(1/2:ℝ))*K^2 := by
    calc
      _ ≤ ∫ ω,Λ^(-ρ)*‖row F ω‖^2 ∂μ := integral_mono hi (hi2.const_mul _) hm
      _ = Λ^(-ρ)*(∫ ω,‖row F ω‖^2 ∂μ) := integral_const_mul _ _
      _ ≤ Λ^(-ρ)*(GaussianNegativePacket.traceConstant*t^(-(1/2:ℝ))*K^2) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hΛ0.le _)
      _ = _ := by ring
  exact ⟨hi,hf,hmass⟩

end SHE.RandomRowEnergy
