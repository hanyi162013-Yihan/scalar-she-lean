module

public import SHEStochastic.ScalarPredictableNormStop
public import SHEStochastic.ScalarHeatFourierEnergy
public import SHEStochastic.BoundedFourierInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedHeatFourierInput
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "w" => NativeFourierHeatCoordinate.weight
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (N : ℕ) (T : ℝ≥0)

local notation "τ" => ContinuousNormExit.exit W N
local notation "A" => 4*(‖g 0‖+(C : ℝ))^2

def before : Set (ℝ≥0×Ω) := StoppedItoInputs.before (Ω := Ω) T ∩
  {p | (p.1 : WithTop ℝ≥0) < τ p.2}

/-- The actual heat-convolution Fourier row uses the original state
on the entire surviving time interval. -/
def row (a : ℂ →L[ℝ] ℝ) (n : ℤ) : ℝ≥0×Ω → Noise :=
  (before W N T).indicator (fun p => Real.exp (-((T : ℝ)-(p.1 : ℝ))*(n : ℝ)^2) •
    StateNoiseCovariance.row ν hβ hβ₁ hg (w a n) (physical W p))

include hW hc in
theorem predictable (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    StronglyMeasurable[F.predictable] (row W hg hβ hβ₁ N T a n) := by
  apply StronglyMeasurable.indicator
  · have hm := ((PredictableClock.real_time_measurable F).const_sub (T : ℝ)).neg.mul_const ((n : ℝ)^2)
    exact hm.exp.stronglyMeasurable.smul
      ((StateNoiseCovariance.row_continuous ν hβ hβ₁ hg (w a n)).comp_stronglyMeasurable
        (physical_predictable F W hW))
  · exact (StoppedItoInputs.before_measurable F T).inter (ScalarPredictableNormStop.predictable F W hW hc N)

include hc in
private theorem norm_sq_cap (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0×Ω) :
    ‖row W hg hβ hβ₁ N T a n p‖^2≤‖w a n‖^2*A*(1+(N : ℝ)^2) := by
  by_cases hp : p∈before W N T
  · have hage : 0 < (T : ℝ)-(p.1 : ℝ) := sub_pos.mpr hp.1
    have hc' : ‖physical W p‖ < (N : ℝ) := by
      rw [physical,LinearIsometry.norm_map]
      exact ContinuousNormExit.before_bound W hc N p.1 p.2 hp.2
    rw [row,Set.indicator_of_mem hp,norm_smul,mul_pow,Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hex : Real.exp (-((T : ℝ)-(p.1 : ℝ))*(n : ℝ)^2)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hage.le) (sq_nonneg _))
    exact (mul_le_of_le_one_left (sq_nonneg _)
      (pow_le_one₀ (Real.exp_nonneg _) hex)).trans
        ((HolderCoefficientEnergyGrowth.row_bound ν hg hβ hβ₁ (w a n) (physical W p)).trans
          (by gcongr))
  · rw [row,Set.indicator_of_notMem hp,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)]
    positivity

include hW hc in
theorem memLp_input (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    MemLp (row W hg hβ hβ₁ N T a n) 2 ((energyMeasure μ H).trim (predictable_le_product F)) := by
  let _ : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  let _ : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
  have hm := predictable F W hW hc hg hβ hβ₁ N T a n
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply Integrable.of_bound (hm.norm.pow 2).aestronglyMeasurable (‖w a n‖^2*A*(1+(N : ℝ)^2))
  apply Filter.Eventually.of_forall
  intro p
  change ‖‖row W hg hβ hβ₁ N T a n p‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact norm_sq_cap W hc hg hβ hβ₁ N T a n p

def input (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Process (E := Noise) F μ H :=
  by
    let _ : MeasurableSpace (ℝ≥0×Ω) := F.predictable
    exact (memLp_input F μ H W hW hc hg hβ hβ₁ N T a n).toLp _

theorem input_ae (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    input F μ H W hW hc hg hβ hβ₁ N T a n =ᵐ[energyMeasure μ H] row W hg hβ hβ₁ N T a n :=
  ae_eq_of_ae_eq_trim (memLp_input F μ H W hW hc hg hβ hβ₁ N T a n).coeFn_toLp

omit [MeasurableSpace Ω] in
open Classical in
/-- The two real coordinates retain the same heat damping and the
same spatial coefficient energy on the actual random time support. -/
theorem pair_energy (n : ℤ) (p : ℝ≥0×Ω) :
    ‖row W hg hβ hβ₁ N T Complex.reCLM n p‖^2+
      ‖row W hg hβ hβ₁ N T Complex.imCLM n p‖^2 =
    if p∈before W N T then Real.exp (-(2*((T : ℝ)-(p.1 : ℝ)))*(n : ℝ)^2)*
      ‖HolderCoefficientIntegrability.coefficient hβ hβ₁ hg (physical W p)‖^2 else 0 := by
  by_cases hp : p∈before W N T
  · simp only [row,Set.indicator_of_mem hp,ite_eq_left hp,norm_smul,mul_pow,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
    rw [←mul_add,ScalarHeatFourierEnergy.row_energy hg hβ hβ₁,pow_two,←Real.exp_add]
    congr 2
    ring
  · simp [row,hp]

end SHEStochastic.ScalarStoppedHeatFourierInput
