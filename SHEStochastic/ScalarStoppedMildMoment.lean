module

public import SHEStochastic.ScalarStoppedDriftConvolution
public import SHEStochastic.ScalarStoppedHeatItoEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedMildMoment
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local notation "φ" => NativeFourierHeatCoordinate.coordinate

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)
  (b : ScalarLinearGrowthDriftField.Data H) (a : ℝ≥0 → Ω → ℝ)
  (u₀ : RealL2)

local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁
local notation "D" => ScalarStoppedDriftConvolution.convolution b W a
local notation "S" => NativeHeatObservation.heat

/-- The localized scalar mild Fourier identity with its exact
diffusion, true time support, and literal Bochner drift. -/
def Equation : Prop :=
  ∀ (N : ℕ) (T : ℝ≥0), T≤H → ∀ (ψ : ℂ →L[ℝ] ℝ) (n : ℤ),
    ∀ᵐ ω ∂μ,(T : WithTop ℝ≥0) < ContinuousNormExit.exit W N ω →
      φ ψ n (W T ω-S (T : ℝ) u₀-D N ω T) = J.integral (v N T ψ n) ω

open Classical in
def liveNormSq (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) < ContinuousNormExit.exit W N ω then ‖W t ω‖^2 else 0

open Classical in
def liveGrowth (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) < ContinuousNormExit.exit W N ω then 1+‖W t ω‖^2 else 0

private theorem norm_three {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x+y+z‖^2≤3*(‖x‖^2+‖y‖^2+‖z‖^2) := by
  have h := (norm_add_le (x+y) z).trans (add_le_add (norm_add_le x y) le_rfl)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  nlinarith only [sq_nonneg (‖x‖-‖y‖),sq_nonneg (‖x‖-‖z‖),sq_nonneg (‖y‖-‖z‖)]

/-- A pointwise stopped mild state is bounded by the true heat orbit,
Bochner drift and all actual scalar stochastic Fourier coordinates. -/
theorem path_bound
    (heq : Equation F μ H W hW hc hg hβ hβ₁ J b a u₀)
    (ham : ∀ ω,Measurable (fun s => a s ω)) (ha : ∀ s ω,|a s ω|≤1)
    (N : ℕ) (T : ℝ≥0) (hT : T≤H) :
    ∀ᵐ ω ∂μ,ENNReal.ofReal (liveNormSq W N T ω) ≤
      3*(ENNReal.ofReal (‖u₀‖^2) +
        ENNReal.ofReal ((T : ℝ)*(∫ s,2*(b.growth : ℝ)^2*liveGrowth W N s ω ∂PredictableL2.timeMeasure T)) +
        ∑' n : ℤ,ENNReal.ofReal (((J.integral (v N T Complex.reCLM n)) ω)^2+
          ((J.integral (v N T Complex.imCLM n)) ω)^2)) := by
  filter_upwards [ae_all_iff.mpr (heq N T hT Complex.reCLM),
    ae_all_iff.mpr (heq N T hT Complex.imCLM)] with ω hre him
  by_cases ht : (T : WithTop ℝ≥0) < ContinuousNormExit.exit W N ω
  · let z := W T ω-S (T : ℝ) u₀-D N ω T
    have hsum :
        ENNReal.ofReal (‖z‖^2) = ∑' n : ℤ,ENNReal.ofReal
          (((J.integral (v N T Complex.reCLM n)) ω)^2+((J.integral (v N T Complex.imCLM n)) ω)^2) := by
      have hz := ScalarHeatFourierEnergy.state_energy z
      have hz' (n : ℤ) :
          (φ Complex.reCLM n z)^2+(φ Complex.imCLM n z)^2 =
            ((J.integral (v N T Complex.reCLM n)) ω)^2+((J.integral (v N T Complex.imCLM n)) ω)^2 := by
        have hr := hre n ht
        have hi := him n ht
        change φ Complex.reCLM n z = _ at hr
        change φ Complex.imCLM n z = _ at hi
        rw [hr,hi]
      rw [←hz.2,ENNReal.ofReal_tsum_of_nonneg (fun n => add_nonneg (sq_nonneg _) (sq_nonneg _)) hz.1]
      simp only [hz']
    have hA : ‖S (T : ℝ) u₀‖^2≤‖u₀‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (RealHeat.realHeat_contraction _ _) 2
    have hD := ScalarStoppedDriftConvolution.energy b W a N ω hc (ham ω) (fun s => ha s ω) T
    have hD' : ‖D N ω T‖^2≤(T : ℝ)*(∫ s,2*(b.growth : ℝ)^2*liveGrowth W N s ω ∂PredictableL2.timeMeasure T) := by
      apply hD.trans_eq
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun s => by
        by_cases hs : (s : WithTop ℝ≥0) < ContinuousNormExit.exit W N ω
        · simp only [liveGrowth,ite_eq_left hs]
        · simp only [liveGrowth,ite_eq_right hs,mul_zero]
    have hE : ‖W T ω‖^2≤3*(‖S (T : ℝ) u₀‖^2+‖D N ω T‖^2+‖z‖^2) := by
      have he : S (T : ℝ) u₀+D N ω T+z=W T ω := by
        dsimp only [z]
        abel
      rw [←he]
      exact norm_three _ _ _
    rw [liveNormSq,ite_eq_left ht,←hsum,←ENNReal.ofReal_add (sq_nonneg _) (hD'.trans' (sq_nonneg _)),
      ←ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (hD'.trans' (sq_nonneg _))) (sq_nonneg _),
      ← (by norm_num : ENNReal.ofReal (3 : ℝ) = 3),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤3)]
    exact ENNReal.ofReal_le_ofReal (hE.trans (by linarith only [hA,hD']))
  · simp only [liveNormSq,ite_eq_right ht,ENNReal.ofReal_zero,zero_le]

end SHEStochastic.ScalarStoppedMildMoment
