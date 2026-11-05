module

public import SHEStochastic.ScalarStoppedDriftConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedDriftAlgebra
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "tm" => PredictableL2.timeMeasure
local notation "heat" => NativeHeatObservation.heat

variable {Ω : Type*} [MeasurableSpace Ω] {H : ℝ≥0} (b : ScalarLinearGrowthDriftField.Data H)
  (W : ℝ≥0 → Ω → RealL2) (hc : ∀ ω,Continuous (fun s => W s ω))
  (N : ℕ) (ω : Ω) (t : ℝ≥0)

local notation "x" a:max => ScalarStoppedDriftConvolution.input b W a N ω
local notation "D" a:max => ScalarStoppedDriftConvolution.convolution b W a N ω t
local notation "τ" => ContinuousNormExit.exit W N ω

include hc in
/-- For every bounded multiplier the stopped Bochner heat row is integrable. -/
theorem integrable (a : ℝ≥0 → Ω → ℝ)
    (ham : Measurable (fun s => a s ω)) (ha : ∀ s,|a s ω|≤1) :
    Integrable (fun s : ℝ≥0 => heat ((t : ℝ)-(s : ℝ)) ((x a) s)) (tm t) := by
  have ht : Measurable (fun s : ℝ≥0 => ((t : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale) := by fun_prop
  have hb := (ScalarStoppedDriftConvolution.input_measurable b W a N ω (hc ω) ham).stronglyMeasurable
  let p (s : ℝ≥0) : ℝ×RealL2 :=
    (((t : ℝ)-(s : ℝ))/NativeHeatObservation.timeScale,(x a) s)
  have hp : StronglyMeasurable p := ht.stronglyMeasurable.prodMk hb
  have hm : StronglyMeasurable (fun s : ℝ≥0 => heat ((t : ℝ)-(s : ℝ)) ((x a) s)) := by
    simpa only [p,NativeHeatObservation.heat,Function.comp_apply] using
      RealHeat.continuous_realHeat_action.comp_stronglyMeasurable hp
  let R := 2*(b.growth : ℝ)^2*(1+(N : ℝ)^2)
  have hR : 0≤R := by unfold R; positivity
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.sqrt R)
  refine ae_of_all _ fun s => ?_
  apply (RealHeat.realHeat_contraction _ _).trans
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hR]
  refine (ScalarStoppedDriftConvolution.input_bound b W a N ω ha s).trans ?_
  by_cases hs : (s : WithTop ℝ≥0)<τ
  · rw [ite_eq_left hs]
    have hb := (ContinuousNormExit.before_bound W hc N s ω hs).le
    dsimp only [R]
    gcongr
  · rw [ite_eq_right hs]
    exact hR

omit [MeasurableSpace Ω] in
theorem zero : D (fun _ _ => 0) = 0 := by
  have h (s : ℝ≥0) : (x (fun _ _ => 0)) s=0 := by
    unfold ScalarStoppedDriftConvolution.input
    split <;> simp
  simp only [ScalarStoppedDriftConvolution.convolution,h,map_zero,integral_zero]

include hc in
/-- The stopped ordinary convolutions retain the correction sign. -/
theorem sub (a d : ℝ≥0 → Ω → ℝ)
    (ham : Measurable (fun s => a s ω)) (ha : ∀ s,|a s ω|≤1)
    (hdm : Measurable (fun s => d s ω)) (hd : ∀ s,|d s ω|≤1) :
    D (fun s ω => a s ω-d s ω) = D a-D d := by
  have h (s : ℝ≥0) : (x (fun s ω => a s ω-d s ω)) s=(x a) s-(x d) s := by
    unfold ScalarStoppedDriftConvolution.input
    split <;> simp [sub_smul]
  simp only [ScalarStoppedDriftConvolution.convolution,h,map_sub]
  exact integral_sub (integrable b W hc N ω t a ham ha) (integrable b W hc N ω t d hdm hd)

end SHEStochastic.ScalarStoppedDriftAlgebra
