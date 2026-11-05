module

public import SHE.StoppedUniformScoreMass
public import SHE.RandomFutureInputFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.StoppedRandomScoreMass
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier StoppedGaussianFeatures
  MeasurableGaussianScores ControlledResidualScoreInput
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

def mass (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (q : ℝ)
    (c e : Ω × Domain → ℝ) (ω : Ω) : ℝ :=
  ∫ p, |e (ω, p)| * scoreVariance (stoppedCovariance σ target center (fun p => c (ω, p)) q)
    (stoppedRow σ target center p) ∂historyMeasure q

/-- Applies equally to the full sample sigma algebra and to an observed
past sigma algebra. No rank or covariance inverse regularity is assumed. -/
theorem mass_measurable (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (q : ℝ)
    (c e : Ω × Domain → ℝ) (hc : Measurable c) (he : Measurable e) :
    Measurable (mass σ target center q c e) := by
  have hh := (futureInput_random_measurable σ target center c e hc he q).comp
    (measurable_id.prodMk (measurable_const (a := (0 : HeatCircle))))
  convert! hh using 1
  funext ω
  simp only [mass, Function.comp_apply, id_eq, futureInput, add_zero]

/-- A deterministic dimension/floor cap for the true random input mass.
It is only an integrability bound; sharp energy estimates retain the mass. -/
theorem mass_bound (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (c e : Ω × Domain → ℝ)
    (hc : Measurable c) (he : Measurable e) {ell M E : ℝ} (hell : 0 < ell)
    (hcb : ∀ ω p, ell ≤ c (ω, p) ∧ c (ω, p) ≤ M)
    (hE : 0 ≤ E) (heb : ∀ ω p, |e (ω, p)| ≤ E) (ω : Ω) :
    0 ≤ mass σ target center q c e ω ∧ mass σ target center q c e ω ≤ E * (n : ℝ) / ell := by
  have hcω := hc.comp ((measurable_const (a := ω)).prodMk measurable_id)
  have heω := he.comp ((measurable_const (a := ω)).prodMk measurable_id)
  have hh := StoppedUniformScoreMass.bounded_input σ target center hages q
    (fun p => c (ω, p)) hcω hell (hcb ω) (fun p => e (ω, p)) heω hE (heb ω)
  refine ⟨?_, hh.2⟩
  have hB := StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hcω
    (fun p => ⟨hell.le.trans (hcb ω p).1, (hcb ω p).2⟩)
  have hr := FullResidualFrameRange.row_mem_all_ranges_ae σ target center hages q
    (fun _ : Unit => fun p => c (ω, p)) (fun _ => hcω) hell (fun _ => hcb ω)
  apply integral_nonneg_of_ae
  exact hr.mono (fun p hp => mul_nonneg (abs_nonneg _) (scoreVariance_nonneg hB (hp ())))

/-- Every fixed even moment required by the conditional word budget is
finite, even when the newest future observation has zero remaining age. -/
theorem mass_pow_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (c e : Ω × Domain → ℝ)
    (hc : Measurable c) (he : Measurable e) {ell M E : ℝ} (hell : 0 < ell)
    (hcb : ∀ ω p, ell ≤ c (ω, p) ∧ c (ω, p) ≤ M)
    (hE : 0 ≤ E) (heb : ∀ ω p, |e (ω, p)| ≤ E) (k : ℕ) :
    Integrable (fun ω => (mass σ target center q c e ω) ^ k) μ := by
  have hm := mass_measurable σ target center q c e hc he
  apply (integrable_const ((E * (n : ℝ) / ell) ^ k)).mono'
    (hm.pow_const k).aestronglyMeasurable
  apply ae_of_all
  intro ω
  have hh := mass_bound σ target center hages q c e hc he hell hcb hE heb ω
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hh.1]
  exact pow_le_pow_left₀ hh.1 hh.2 k

end SHE.StoppedRandomScoreMass
