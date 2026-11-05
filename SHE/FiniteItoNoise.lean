module

public import SHE.StoppedItoInputs
public import SHE.PhysicalIto
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The martingale term of finite-dimensional Itô's formula is an
actual ordinary scalar integral. Its predictable L² input and centering
are proved from bounded test gradients and the original noise rows. -/
noncomputable section
namespace SHE.FiniteItoNoise
open MeasureTheory Set PredictableL2 GaussianItoTest StoppedItoInputs
open scoped NNReal ENNReal
abbrev State (n : ℕ) := WordRecursion.State n

def AdmissibleGradient {n : ℕ} (G : ℝ → State n → ℝ) : Prop :=
  Continuous (fun p : ℝ × State n => fderiv ℝ (G p.1) p.2) ∧
    ∃ L : ℝ,∀ t z,‖fderiv ℝ (G t) z‖ ≤ L

theorem regular_admissible {n : ℕ} {a b : ℝ} {G dG : ℝ → State n → ℝ}
    (hG : RegularTest a b G dG) : AdmissibleGradient G := by
  obtain ⟨M,L,B,hb⟩ := hG.bounds
  exact ⟨hG.gradient_continuous,L,fun t z => (hb t z).2.1⟩

variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[𝓕.predictable] Y)
variable (R : Fin n → Process (E := C) 𝓕 μ h)

def gradientCoefficient (G : ℝ → State n → ℝ) (i : Fin n) (p : ℝ≥0 × Ω) : ℝ :=
  fderiv ℝ (G (p.1:ℝ)) (Y p) (EuclideanSpace.basisFun (Fin n) ℝ i)

include hY in
theorem gradientCoefficient_predictable {G : ℝ → State n → ℝ} (hG : AdmissibleGradient G) (i : Fin n) :
    StronglyMeasurable[𝓕.predictable] (gradientCoefficient Y G i) := by
  have hc := hG.1.clm_apply (continuous_const (y := EuclideanSpace.basisFun (Fin n) ℝ i))
  have hm := hc.measurable.comp ((PredictableClock.real_time_measurable 𝓕).prodMk hY.measurable)
  exact hm.stronglyMeasurable

theorem gradientCoefficient_bound {G : ℝ → State n → ℝ} {L : ℝ}
    (hL : ∀ t z,‖fderiv ℝ (G t) z‖ ≤ L) (i : Fin n) (p : ℝ≥0 × Ω) :
    ‖gradientCoefficient Y G i p‖ ≤ L := by
  calc
    _ ≤ ‖fderiv ℝ (G (p.1:ℝ)) (Y p)‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
      (fderiv ℝ (G (p.1:ℝ)) (Y p)).le_opNorm _
    _ = ‖fderiv ℝ (G (p.1:ℝ)) (Y p)‖ := by
      rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]
    _ ≤ L := hL _ _

def gradientRow (G : ℝ → State n → ℝ) (p : ℝ≥0 × Ω) : C :=
  ∑ i : Fin n,gradientCoefficient Y G i p • R i p

include hY in
theorem gradientRow_predictable {G : ℝ → State n → ℝ} (hG : AdmissibleGradient G) :
    StronglyMeasurable[𝓕.predictable] (gradientRow 𝓕 μ h Y R G) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact (gradientCoefficient_predictable 𝓕 Y hY hG i).smul (Lp.stronglyMeasurable (R i))

include hY in
theorem gradientRow_memLp {G : ℝ → State n → ℝ} (hG : AdmissibleGradient G) :
    @MemLp _ _ 𝓕.predictable _ _ (gradientRow 𝓕 μ h Y R G) 2
      ((energyMeasure μ h).trim (predictable_le_product 𝓕)) := by
  obtain ⟨L,hL⟩ := hG.2
  apply memLp_finsetSum
  intro i _
  apply (Lp.memLp (R i)).of_le_mul (c := L)
    ((gradientCoefficient_predictable 𝓕 Y hY hG i).smul (Lp.stronglyMeasurable (R i))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    change ‖gradientCoefficient Y G i p • R i p‖ ≤ L*‖R i p‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (gradientCoefficient_bound Y hL i p) (norm_nonneg _))

def gradientProcess (G : ℝ → State n → ℝ) (hG : AdmissibleGradient G) : Process (E := C) 𝓕 μ h :=
  (gradientRow_memLp 𝓕 μ h Y hY R hG).toLp (gradientRow 𝓕 μ h Y R G)

theorem gradientProcess_ae (G : ℝ → State n → ℝ) (hG : AdmissibleGradient G) :
    gradientProcess 𝓕 μ h Y hY R G hG =ᵐ[energyMeasure μ h] gradientRow 𝓕 μ h Y R G :=
  ae_eq_of_ae_eq_trim (gradientRow_memLp 𝓕 μ h Y hY R hG).coeFn_toLp

open Classical in
def noise (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) (a b : ℝ)
    (G : ℝ → State n → ℝ) : Lp ℝ 2 μ :=
  if hG : AdmissibleGradient G then
    J.integral (stop 𝓕 μ h b (gradientProcess 𝓕 μ h Y hY R G hG)-
      stop 𝓕 μ h a (gradientProcess 𝓕 μ h Y hY R G hG))
  else 0

theorem noise_eq (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) (a b : ℝ)
    (G : ℝ → State n → ℝ) (hG : AdmissibleGradient G) :
    noise 𝓕 μ h Y hY R J a b G =
      J.integral (stop 𝓕 μ h b (gradientProcess 𝓕 μ h Y hY R G hG)-
        stop 𝓕 μ h a (gradientProcess 𝓕 μ h Y hY R G hG)) := by
  rw [noise,dif_pos hG]

theorem noise_centered (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) (a b : ℝ)
    (G : ℝ → State n → ℝ) : (∫ ω,noise 𝓕 μ h Y hY R J a b G ω ∂μ)=0 := by
  classical
  by_cases hG : AdmissibleGradient G
  · rw [noise_eq 𝓕 μ h Y hY R J a b G hG]
    exact J.centered _
  · rw [noise,dif_neg hG]
    exact integral_eq_zero_of_ae (Lp.coeFn_zero ℝ 2 μ)

theorem noise_integrable [IsFiniteMeasure μ]
    (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) (a b : ℝ)
    (G : ℝ → State n → ℝ) : Integrable (noise 𝓕 μ h Y hY R J a b G) μ :=
  (Lp.memLp _).integrable (by norm_num : (1:ENNReal) ≤ 2)

end SHE.FiniteItoNoise
