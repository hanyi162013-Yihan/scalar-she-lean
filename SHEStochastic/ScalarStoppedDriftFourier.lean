module

public import SHEStochastic.ScalarStoppedDriftConvolution
public import SHEStochastic.ScalarGirsanovDriftPairing
public import SHEStochastic.ScalarStoppedHeatFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedDriftFourier
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "tm" => PredictableL2.timeMeasure
local notation "heat" => NativeHeatObservation.heat

variable {Ω : Type*} [MeasurableSpace Ω] {H : ℝ≥0} (b : ScalarLinearGrowthDriftField.Data H)
  (W : ℝ≥0 → Ω → RealL2) (hc : ∀ ω,Continuous (fun s => W s ω))
  (a : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω)
  (ham : Measurable (fun s => a s ω)) (ha : ∀ s,|a s ω|≤1) (t : ℝ≥0)

local notation "D" => ScalarStoppedDriftConvolution.convolution b W a N ω t
local notation "τ" => ContinuousNormExit.exit W N ω
local notation "x" => ScalarStoppedDriftConvolution.input b W a N ω

include hc ham ha in
/-- The actual Bochner convolution and its stochastic shift use the same
physical Fourier mode, age, and strict state-exit condition. -/
theorem coordinate (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    φ ψ n D =
      ∫ s, if (s : ℝ)<t ∧ (s : WithTop ℝ≥0)<τ then
        Real.exp (-((t : ℝ)-(s : ℝ))*(n : ℝ)^2)*a s ω*
          φ ψ n (ScalarLinearGrowthDriftField.field b (s,W s ω)) else 0 ∂tm t := by
  classical
  let v (s : ℝ≥0) := heat ((t : ℝ)-(s : ℝ)) (x s)
  have hm : StronglyMeasurable v := by
    have ht : Measurable (fun s : ℝ≥0 => ((t : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale) := by fun_prop
    have hb := (ScalarStoppedDriftConvolution.input_measurable b W a N ω (hc ω) ham).stronglyMeasurable
    let p (s : ℝ≥0) : ℝ×RealL2 :=
      (((t : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale,x s)
    have hp : StronglyMeasurable p := ht.stronglyMeasurable.prodMk hb
    simpa only [v,p,NativeHeatObservation.heat,Function.comp_apply] using
      RealHeat.continuous_realHeat_action.comp_stronglyMeasurable hp
  let R := 2*(b.growth : ℝ)^2*(1+(N : ℝ)^2)
  have hR : 0≤R := by unfold R; positivity
  have hcap (s : ℝ≥0) : ‖x s‖^2≤R := by
    refine (ScalarStoppedDriftConvolution.input_bound b W a N ω ha s).trans ?_
    by_cases hs : (s : WithTop ℝ≥0)<τ
    · rw [ite_eq_left hs]
      have hb := (ContinuousNormExit.before_bound W hc N s ω hs).le
      dsimp only [R]
      gcongr
    · rw [ite_eq_right hs]
      exact hR
  have hi : Integrable v (tm t) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Real.sqrt R)
    refine ae_of_all _ fun s => ?_
    apply (RealHeat.realHeat_contraction _ _).trans
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hR]
    exact hcap s
  rw [ScalarStoppedDriftConvolution.convolution,show (fun s : ℝ≥0 => heat ((t : ℝ)-(s : ℝ)) (x s))=v from rfl,
    ←(φ ψ n).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [timeMeasure_ae_mem t,(tm t).ae_ne t] with s hs hst
  have hst' : (s : ℝ)<t := by exact_mod_cast lt_of_le_of_ne hs.2 hst
  change φ ψ n (heat ((t : ℝ)-(s : ℝ)) (x s))=_
  rw [NativeFourierHeatCoordinate.coordinate_heat ψ n (sub_nonneg.mpr hst'.le)]
  by_cases h : (s : WithTop ℝ≥0)<τ
  · simp only [ScalarStoppedDriftConvolution.input,ite_eq_left h,hst',true_and,map_smul,
      smul_eq_mul,mul_assoc]
  · simp only [ScalarStoppedDriftConvolution.input,ite_eq_right h,hst',true_and,map_zero,mul_zero]

end SHEStochastic.ScalarStoppedDriftFourier
