module

public import SHEStochastic.ScalarStoppedHeatFourierInput
public import SHE.StoppedInputAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedHeatClock
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))

local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (N : ℕ) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)

local notation "v" t:max => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁ N t ψ n
local notation "R" t:max => ScalarStoppedHeatFourierInput.row W hg hβ hβ₁ N t ψ n
local notation "S" t:max => ScalarStoppedHeatFourierInput.before W N t
local notation "stop" => StoppedItoInputs.stop F μ H

/-- At each earlier time the stopped convolution row is exactly a
deterministic Fourier multiplier times the prefix of its horizon row. -/
theorem input_eq (t : ℝ≥0) (ht : t≤H) :
    v t = Real.exp (((H : ℝ)-(t : ℝ))*(n : ℝ)^2) • stop t (v H) := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product F)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hsm := ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.exp (((H : ℝ)-(t : ℝ))*(n : ℝ)^2)) (stop t (v H)))
  filter_upwards [ScalarStoppedHeatFourierInput.input_ae F μ H W hW hc hg hβ hβ₁ N t ψ n,
    ScalarStoppedHeatFourierInput.input_ae F μ H W hW hc hg hβ hβ₁ N H ψ n,
    StoppedItoInputs.stop_ae F μ H t (v H),hsm] with p hvt hvH hst hsm
  rw [hvt,hsm,Pi.smul_apply,hst]
  by_cases hp : p ∈ StoppedItoInputs.before (Ω := Ω) t
  · rw [indicator_of_mem hp,hvH]
    by_cases he : (p.1 : WithTop ℝ≥0)<ContinuousNormExit.exit W N p.2
    · have hpH : p∈StoppedItoInputs.before (Ω := Ω) H := by
        exact (show (p.1 : ℝ)<t from hp).trans_le (by exact_mod_cast ht)
      have ht' : p∈S t := ⟨hp,he⟩
      have hH' : p∈S H := ⟨hpH,he⟩
      rw [ScalarStoppedHeatFourierInput.row,ScalarStoppedHeatFourierInput.row,
        indicator_of_mem ht',indicator_of_mem hH',smul_smul,←Real.exp_add]
      congr 2
      ring
    · have ht' : p∉S t := fun h => he h.2
      have hH' : p∉S H := fun h => he h.2
      rw [ScalarStoppedHeatFourierInput.row,ScalarStoppedHeatFourierInput.row,
        indicator_of_notMem ht',indicator_of_notMem hH',smul_zero]
  · rw [indicator_of_notMem hp,smul_zero,ScalarStoppedHeatFourierInput.row,
      indicator_of_notMem (show p∉S t from fun h => hp h.1)]

theorem stop_input (t : ℝ≥0) (ht : t≤H) : stop t (v t)=v t := by
  rw [input_eq F μ H W hW hc hg hβ hβ₁ N ψ n t ht,StoppedInputAlgebra.stop_smul,
    StoppedInputAlgebra.stop_stop,min_self]

end SHEStochastic.ScalarStoppedHeatClock
