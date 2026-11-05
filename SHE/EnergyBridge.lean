module

public import SHE.HaarDamping
public import SHE.FullMaster

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.EnergyBridge
open MeasureTheory Set SHE.FiniteHaar SHE.CircleHeat
open scoped ENNReal
local instance : MeasurableSpace CircleL2 := borel CircleL2
local instance : BorelSpace CircleL2 := ⟨rfl⟩

/-- An extended nonnegative energy inequality gives an actual finite real
inequality once the input energy is finite. -/
theorem real_energy_bound {X F : ℝ≥0∞} {A : ℝ} (hA : 0 ≤ A)
    (hF : F ≠ ∞) (h : X ≤ ENNReal.ofReal A*F) :
    X ≠ ∞ ∧ X.toReal ≤ A*F.toReal := by
  have hfin : ENNReal.ofReal A*F ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF
  refine ⟨ne_top_of_le_ne_top hfin h,?_⟩
  have hh := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hA] using hh

theorem sqrt_rpow_energy {Λ ρ : ℝ} (hΛ : 0 < Λ) :
    Real.sqrt (Λ^(ρ-1/2)) = Λ^(ρ/2-1/4) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hΛ.le]
  congr 1
  ring

/-- This is the unsquared scaling used in the manuscript's master
inequality, derived from the true squared stochastic energy estimate. -/
theorem root_energy_bound {X F : ℝ≥0∞} {A Λ ρ K : ℝ}
    (hA : 0 ≤ A) (hΛ : 0 < Λ) (hK : 0 ≤ K) (hF : F ≠ ∞)
    (hFK : F.toReal ≤ K^2) (h : X ≤ ENNReal.ofReal (A*Λ^(ρ-1/2))*F) :
    X ≠ ∞ ∧ Real.sqrt X.toReal ≤ Real.sqrt A*Λ^(ρ/2-1/4)*K := by
  have hscale : 0 ≤ A*Λ^(ρ-1/2) := mul_nonneg hA (Real.rpow_nonneg hΛ.le _)
  obtain ⟨hfin,hb⟩ := real_energy_bound hscale hF h
  refine ⟨hfin,?_⟩
  calc
    _ ≤ Real.sqrt (A*Λ^(ρ-1/2)*K^2) := Real.sqrt_le_sqrt
      (hb.trans (mul_le_mul_of_nonneg_left hFK hscale))
    _ = _ := by rw [Real.sqrt_mul hscale,Real.sqrt_sq hK,
      Real.sqrt_mul hA,sqrt_rpow_energy hΛ]

def inputEnergy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (κ Λ ρ T : ℝ) (f g : Ω → ℝ → CircleL2) : ℝ≥0∞ :=
  ∫⁻ ω,(∫⁻ s in Ioc (0:ℝ) T,ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ (f ω s-g ω s))) ∂μ

def outputEnergy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℝ) (Z : Ω → ℝ → CircleL2) : ℝ≥0∞ :=
  ∫⁻ ω,(∫⁻ t in Ioc (0:ℝ) T,ENNReal.ofReal (‖Z ω t‖^2)) ∂μ

theorem signedDampingConstant_pos {ρ : ℝ} (hρ : ρ < 1/2) : 0 < signedDampingConstant ρ := by
  unfold signedDampingConstant
  have h₁ := dampingPowerConstant_pos (by norm_num : (0:ℝ)<1/2)
  have h₂ := dampingPowerConstant_pos (by linarith : 0<1/2-ρ)
  linarith

/-- For the actual infinite signed Haar columns, the only stochastic
premise is their exact standard isometry. All analytic constants, energy
finiteness and the square-root passage are proved. -/
theorem actual_haar_energy_relation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (f g : Ω → ℝ → CircleL2) (m U : ℝ) (hm : 0 < m) (hU : 0 ≤ U)
    (hfreal : ∀ ω s,∀ᵐ y ∂AddCircle.haarAddCircle,(f ω s y).im=0)
    (hgreal : ∀ ω s,∀ᵐ y ∂AddCircle.haarAddCircle,(g ω s y).im=0)
    (hf : ∀ ω s,∀ᵐ y ∂AddCircle.haarAddCircle,m≤(f ω s y).re ∧ (f ω s y).re≤U)
    (hg : ∀ ω s,∀ᵐ y ∂AddCircle.haarAddCircle,m≤(g ω s y).re ∧ (g ω s y).re≤U)
    (hmf : ∀ ω,Measurable (f ω)) (hmg : ∀ ω,Measurable (g ω)) (T e : ℝ) (he : 0 ≤ e)
    (Z : Ω → ℝ → CircleL2)
    (hIsometry : outputEnergy μ T Z = ∫⁻ ω,(∫⁻ t in Ioc (0:ℝ) T,
      ∫⁻ s in Ioo (0:ℝ) t,ENNReal.ofReal (Real.exp (-2*Λ*(t-s))*
        globalSignedHeatEnergy (f ω s) (g ω s) (t-s))) ∂μ) :
    outputEnergy μ T Z ≠ ∞ ∧
      Real.sqrt (outputEnergy μ T Z).toReal ≤
        Real.sqrt (signedHeatSqConstant κ ρ m U*signedDampingConstant ρ)*
          Λ^(ρ/2-1/4)*Real.sqrt ((inputEnergy μ κ Λ ρ T f g).toReal+e) := by
  have hΛpos := zero_lt_one.trans_le hΛ
  have hi := elliptic_random_input_energy (κ:=κ) μ hΛpos hρ.le f g m U T
    hfreal hgreal hf hg
  have hfin : inputEnergy μ κ Λ ρ T f g ≠ ∞ := by
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hi
  have hs := signed_global_stochastic_energy_of_isometry μ hκ hΛ hρ hρhalf f g m U hm
    hfreal hgreal hf hg hmf hmg T Z hIsometry
  have hA : 0 ≤ signedHeatSqConstant κ ρ m U*signedDampingConstant ρ :=
    mul_nonneg (signedHeatSqConstant_nonneg hκ hρ hρhalf hU) (signedDampingConstant_pos hρhalf).le
  apply root_energy_bound hA hΛpos (Real.sqrt_nonneg _) hfin ?_ hs
  rw [Real.sq_sqrt (by positivity)]
  linarith

end SHE.EnergyBridge
