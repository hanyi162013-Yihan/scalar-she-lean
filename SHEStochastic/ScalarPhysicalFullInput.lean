module

public import SHEStochastic.ScalarPhysicalStoppedEquation
public import SHEStochastic.HolderCoefficientEnergyGrowth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalFullInput
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "haar" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 haar
local notation "r" => NativeClock.rate
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (t : ℝ≥0) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ)

local notation "k" => NativeFourierHeatCoordinate.weight ψ n

def row (p : ℝ≥0×Ω) : Noise :=
  (StoppedItoInputs.before (Ω := Ω) t).indicator
    (fun q => Real.exp (-((r : ℝ)*((t : ℝ)-(q.1 : ℝ)))*(n : ℝ)^2) •
      StateNoiseCovariance.row haar hβ hβ₁ hg k (physical W q)) p

include hW in
theorem predictable : StronglyMeasurable[F.predictable] (row W hg hβ hβ₁ t ψ n) := by
  have ht : @Measurable (ℝ≥0×Ω) ℝ F.predictable _ (fun p => (p.1 : ℝ)) :=
    PredictableClock.real_time_measurable F
  have hs : MeasurableSet[F.predictable] (StoppedItoInputs.before (Ω := Ω) (t : ℝ)) :=
    ht measurableSet_Iio
  have hm : @Measurable (ℝ≥0×Ω) ℝ F.predictable _
      (fun q => Real.exp (-((r : ℝ)*((t : ℝ)-(q.1 : ℝ)))*(n : ℝ)^2)) :=
    (((measurable_const.sub ht).const_mul (r : ℝ)).neg.mul_const ((n : ℝ)^2)).exp
  exact (hm.stronglyMeasurable.smul
    ((StateNoiseCovariance.row_continuous haar hβ hβ₁ hg k).comp_stronglyMeasurable
      (physical_predictable F W hW))).indicator hs

omit [MeasurableSpace Ω] in
theorem norm_bound (p : ℝ≥0×Ω) :
    ‖row W hg hβ hβ₁ t ψ n p‖^2≤
      (‖k‖^2*(4*(‖g 0‖+(C : ℝ))^2))*(1+‖W p.1 p.2‖^2) := by
  by_cases hp : p∈StoppedItoInputs.before (Ω := Ω) (t : ℝ)
  · have ha : 0≤(t : ℝ)-(p.1 : ℝ) := sub_nonneg.mpr (le_of_lt hp)
    have hn : 0≤(r : ℝ)*((t : ℝ)-(p.1 : ℝ))*(n : ℝ)^2 := by positivity
    have he : Real.exp (-((r : ℝ)*((t : ℝ)-(p.1 : ℝ)))*(n : ℝ)^2)≤1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    rw [row,indicator_of_mem hp,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
    have h := HolderCoefficientEnergyGrowth.row_bound haar hg hβ hβ₁ k (physical W p)
    rw [physical,LinearIsometry.norm_map] at h
    exact (mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (Real.exp_pos _).le he)).trans h
  · rw [row,indicator_of_notMem hp,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)]
    positivity

include hW in
theorem memLp (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H)) :
    @MemLp _ _ F.predictable _ _ (row W hg hβ hβ₁ t ψ n) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hm := predictable F W hW hg hβ hβ₁ t ψ n
  have ha := (hm.mono (predictable_le_product F)).aestronglyMeasurable (μ := energyMeasure μ H)
  have hi : Integrable (fun p => ‖row W hg hβ hβ₁ t ψ n p‖^2) (energyMeasure μ H) := by
    let _ : IsFiniteMeasure (energyMeasure μ H) := by unfold energyMeasure; infer_instance
    apply (((integrable_const (1 : ℝ)).add hM).const_mul (‖k‖^2*(4*(‖g 0‖+(C : ℝ))^2))).mono'
      (ha.norm.pow 2)
    exact ae_of_all _ (fun p => by
      change ‖‖row W hg hβ hβ₁ t ψ n p‖^2‖ ≤
        (‖k‖^2*(4*(‖g 0‖+(C : ℝ))^2))*(1+‖W p.1 p.2‖^2)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact norm_bound W hg hβ hβ₁ t ψ n p)
  exact (eLpNorm_trim (predictable_le_product F) hm).trans_lt
    ((memLp_two_iff_integrable_sq_norm ha).mpr hi)

def input (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H)) :
    Process (E := Noise) F μ H :=
  (memLp F μ H W hW hg hβ hβ₁ t ψ n hM).toLp (row W hg hβ hβ₁ t ψ n)

theorem input_ae (hM : Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H)) :
    input F μ H W hW hg hβ hβ₁ t ψ n hM =ᵐ[energyMeasure μ H] row W hg hβ hβ₁ t ψ n :=
  ae_eq_of_ae_eq_trim (memLp F μ H W hW hg hβ hβ₁ t ψ n hM).coeFn_toLp

end SHEStochastic.ScalarPhysicalFullInput
