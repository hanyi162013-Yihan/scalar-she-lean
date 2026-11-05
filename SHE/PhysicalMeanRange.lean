module

public import SHE.StoppedMeanRange
public import SHE.PhysicalProfile
public import SHE.HeatMarkov

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalMeanRange
open Set MeasureTheory AddCircle Real Finset StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  GaussianIncrement StoppedMeanEnergy RealHeatCovarianceMean StoppedMeanRange PhysicalProfile
open scoped InnerProductSpace
local instance physicalMeanRange_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def currentDirection (target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (d : StoppedFourier.CircleL2) : State n :=
  WithLp.toLp 2 (fun i => physicalHeatMean d (target i - q, nativeCenter a i))

def dampedDirection (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q Λ : ℝ)
    (d : StoppedFourier.CircleL2) : State n :=
  WithLp.toLp 2 (fun i => exp (-Λ * (σ i - q)) * physicalHeatMean d (target i - q, nativeCenter a i))

theorem currentDirection_eq (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hage : ∀ i, target i - q = 4 * π ^ 2 * t i)
    (act : ∀ i, q < σ i) (d : StoppedFourier.CircleL2) :
    currentDirection target a q d = meanDirection (currentSynthesis σ target a q t hage act)
      (CircleNormalization.push.symm d) := by
  apply PiLp.ext
  intro i
  rw [meanDirection_apply, currentSynthesis_basis]
  change physicalHeatMean d (target i - q, nativeCenter a i) =
    (inner ℂ (unitHeatKernel (t i) (a i)) (CircleNormalization.push.symm d)).re
  rw [physicalHeatMean_eq (by rw [hage i]; exact mul_pos (by positivity) (ht i))]
  have hi := CircleNormalization.push.inner_map_map (unitHeatKernel (t i) (a i)) (CircleNormalization.push.symm d)
  rw [HeatMarkov.push_unitHeatKernel, LinearIsometryEquiv.apply_symm_apply, ← hage i] at hi
  exact congrArg Complex.re hi

theorem dampedDirection_eq (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q Λ : ℝ)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hage : ∀ i, target i - q = 4 * π ^ 2 * t i)
    (act : ∀ i, q < σ i) (d : StoppedFourier.CircleL2) :
    dampedDirection σ target a q Λ d = meanDirection (dampedSynthesis σ target a q Λ t hage act)
      (CircleNormalization.push.symm d) := by
  apply PiLp.ext
  intro i
  rw [meanDirection_apply, dampedSynthesis_basis]
  change exp (-Λ * (σ i - q)) * physicalHeatMean d (target i - q, nativeCenter a i) =
    (inner ℂ ((exp (-Λ * (σ i - q)) : ℂ) • unitHeatKernel (t i) (a i)) (CircleNormalization.push.symm d)).re
  rw [physicalHeatMean_eq (by rw [hage i]; exact mul_pos (by positivity) (ht i)), inner_smul_left]
  have hi := CircleNormalization.push.inner_map_map (unitHeatKernel (t i) (a i)) (CircleNormalization.push.symm d)
  rw [HeatMarkov.push_unitHeatKernel, LinearIsometryEquiv.apply_symm_apply, ← hage i] at hi
  rw [← hi]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem currentDirection_mem_range (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q : ℝ)
    (hages : ∀ i, σ i ≤ target i) (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, q + δ ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d : StoppedFourier.CircleL2) :
    currentDirection target a q d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ target (nativeCenter a) c q)).range := by
  let t : Fin n → ℝ := fun i => (target i - q) / (4 * π ^ 2)
  have ht : ∀ i, 0 < t i := fun i => div_pos (by linarith [hstop i, hages i]) (by positivity)
  have he : ∀ i, target i - q = 4 * π ^ 2 * t i := by intro i; dsimp [t]; field_simp
  have ha : ∀ i, q < σ i := fun i => by linarith [hstop i]
  rw [currentDirection_eq σ target a q t ht he ha d]
  exact (current_mean_range σ target a q t he hages δ hδ hstop c hc U ell hcb hell hcl _).1

theorem dampedDirection_mem_range (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (q Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hages : ∀ i, σ i ≤ target i) (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, q + δ ≤ σ i)
    (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 < ell) (hcl : ∀ p, ell ≤ c p)
    (d : StoppedFourier.CircleL2) :
    dampedDirection σ target a q Λ d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (stoppedCovariance σ target (nativeCenter a) c q)).range := by
  by_cases h0 : Λ = 0
  · simpa only [h0, dampedDirection, currentDirection, neg_zero, zero_mul, exp_zero, one_mul] using
      currentDirection_mem_range σ target a q hages δ hδ hstop c hc U ell hcb hell hcl d
  let t : Fin n → ℝ := fun i => (target i - q) / (4 * π ^ 2)
  have ht : ∀ i, 0 < t i := fun i => div_pos (by linarith [hstop i, hages i]) (by positivity)
  have he : ∀ i, target i - q = 4 * π ^ 2 * t i := by intro i; dsimp [t]; field_simp
  have ha : ∀ i, q < σ i := fun i => by linarith [hstop i]
  rw [dampedDirection_eq σ target a q Λ t ht he ha d]
  exact (damped_mean_range σ target a q Λ (lt_of_le_of_ne hΛ (Ne.symm h0)) t he hages δ hδ hstop c hc U ell hcb hell hcl _).1

theorem exists_positive_gap (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ σ i := by
  have hh : ∀ s : Finset (Fin n), ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ σ i := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨δ, hδ, hs⟩ := ih
      refine ⟨min (σ i) δ, lt_min (hσ i) hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hs j hj)
  obtain ⟨δ, hδ, hh⟩ := hh univ
  exact ⟨δ, hδ, fun i => hh i (mem_univ i)⟩

end SHE.PhysicalMeanRange
