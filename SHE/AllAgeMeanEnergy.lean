module

public import SHE.StoppedBlockEnergy
public import SHE.AgePartition
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Collision-uniform all-age spatial energy for the actual canonical
Gaussian score of a physical damped mean. Here stops equal targets, as in
native point observations; no target/stopping-age identification is made
for contracted observations. -/
namespace SHE.AllAgeMeanEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks
  StoppedBlockMean StoppedBlockEnergy RealHeatCovarianceMean MeasurableGaussianScores
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem block_term_bound {lo s scale M : ℝ} (hs : 0 < s) (hlo : s ≤ lo)
    (hscale : 1 ≤ scale) (θ : ℝ) (d : HeatTorus.CircleL2) :
    (2 / lo) * sqrt M * sqrt (lo / scale) * ‖CircleHeat.heat (θ * (lo / scale)) d‖ ^ 2 ≤
      (2 * sqrt M / sqrt s) * ‖d‖ ^ 2 := by
  have hl : 0 < lo := hs.trans_le hlo
  have hsl : 0 < sqrt lo := sqrt_pos.mpr hl
  have hss : 0 < sqrt s := sqrt_pos.mpr hs
  have hroot : sqrt (lo / scale) ≤ sqrt lo :=
    sqrt_le_sqrt (div_le_self hl.le hscale)
  have hcoef : (2 / lo) * sqrt M * sqrt (lo / scale) ≤ 2 * sqrt M / sqrt s := by
    calc
      _ ≤ (2 / lo) * sqrt M * sqrt lo := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 2 * sqrt M / sqrt lo := by
        have he := sq_sqrt hl.le
        field_simp
        rw [he]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hss (sqrt_le_sqrt hlo)
  have hn : ‖CircleHeat.heat (θ * (lo / scale)) d‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (CircleHeat.heat_contraction _ d) 2
  exact mul_le_mul hcoef hn (sq_nonneg _) (by positivity)

/-- Uniform all-age native point mean energy against the actual weighted
full stopped covariance, with arbitrary collisions and positive damping. -/
theorem native_point_mean_energy (n : ℕ) (hn : 0 < n) :
    ∃ h C : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < C ∧
      ∀ (target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
      (s : ℝ) (hs : 0 < s) (hmin : ∀ i, s ≤ target i - u),
      ∀ (c : UnitAddCircle × Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
      (hcb : ∀ x p, 0 ≤ c (x,p) ∧ c (x,p) ≤ U), 0 < ell → (∀ x p, ell ≤ c (x,p)) →
      ∀ d : HeatTorus.CircleL2,
      let act : ∀ i, u < target i := fun i => by linarith [hmin i]
      let S := fun x => dampedSynthesis target target (fun i => a i + x) u Λ t hage act
      let V := fun x => StoppedGaussianFeatures.stoppedCovariance target target
        (nativeCenter (fun i => a i + x)) (fun p => c (x,p)) u
      Integrable (fun x => scoreVariance (V x) (meanDirection (S x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (V x) (meanDirection (S x) d) ∂haarAddCircle) ≤
        (C / ell) * (sqrt s)⁻¹ * ‖d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, he⟩ := translated_physical_block_mean_energy n
  let A : ℝ := 4 * (n : ℝ) ^ 2 + 1
  let M : ℝ := A ^ n
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg (n : ℝ)]
  have hM : 1 ≤ M := one_le_pow₀ hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨h, 4 * K * (n : ℝ) * sqrt M, hh, hh1, by positivity, ?_⟩
  intro target a u Λ hΛ t ht hth hage s hs hmin c hc U ell hcb hell hcl d
  let ages : Fin n → ℝ := fun i => target i - u
  have hagespos (i : Fin n) : 0 < ages i := hs.trans_le (hmin i)
  obtain ⟨P⟩ := AgeClustering.exists_partition ages hagespos hA
  have hg := P.count_pos hn
  have hscale : 0 < 4 * π ^ 2 := by positivity
  have hscale1 : 1 ≤ 4 * π ^ 2 := by nlinarith [pi_gt_three]
  have hPA : 4 * (P.count : ℝ) ^ 2 + 1 ≤ A := by
    have hh : (P.count : ℝ) ≤ n := by exact_mod_cast P.count_le
    dsimp [A]
    nlinarith [show (0 : ℝ) ≤ P.count by positivity]
  let w := fun j => P.lower j / (4 * π ^ 2)
  have hw (j : Fin P.count) : 0 < w j := div_pos (P.lower_pos j) hscale
  have hlo (i : Fin n) : w (P.label i) ≤ t i := by
    apply (div_le_iff₀ hscale).mpr
    have hp := P.lower_bound i
    change P.lower (P.label i) ≤ target i - u at hp
    rw [hage i] at hp
    nlinarith
  have hhi (i : Fin n) : t i ≤ M * w (P.label i) := by
    have hp := (P.upper_bound i).trans (P.ratio (P.label i))
    change target i - u ≤ M * P.lower (P.label i) at hp
    rw [hage i] at hp
    dsimp [w]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hscale).mpr
    convert! hp using 1; ring
  have hstoplo (i : Fin n) : u + P.lower (P.label i) ≤ target i := by
    have hp := P.lower_bound i
    change P.lower (P.label i) ≤ target i - u at hp
    linarith
  have hstophi (i : Fin n) : target i ≤ u + P.upper (P.label i) := by
    have hp := P.upper_bound i
    change target i - u ≤ P.upper (P.label i) at hp
    linarith
  let act : ∀ j i, u < groupData P.label P.rep target j i := fun j i => by
    have hp := (groupData_bounds P.label P.rep P.label_rep target
      (fun j => u + P.lower j) (fun j => u + P.upper j) hstoplo hstophi j i).1
    linarith [P.lower_pos j]
  have hb := he hg P.label P.rep P.label_rep target target a u Λ hΛ t ht hth hage (fun _ => le_rfl)
    P.lower P.upper A hPA P.lower_pos P.lower_le_upper hstoplo hstophi P.separation
    w (fun _ => M) hw (fun _ => hM) hlo hhi c hc U ell hcb hell hcl d
  have hsum (x : UnitAddCircle) := blockMean_sum P.label P.rep target target (fun i => a i + x)
    u Λ t hage act (fun i => by linarith [hmin i])
  change ∀ x, (∑ j, blockMean P.label P.rep target target (fun i => a i + x) u Λ t hage act j) = _ at hsum
  simp_rw [hsum] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hterm (j : Fin P.count) :
      (2 / P.lower j) * sqrt M * sqrt (w j) * ‖CircleHeat.heat (θ * w j) d‖ ^ 2 ≤
        (2 * sqrt M / sqrt s) * ‖d‖ ^ 2 := by
    apply block_term_bound hs _ hscale1 θ d
    rw [P.lower_eq_rep]
    exact hmin _
  calc
    _ ≤ (K / (ell / 2)) * ∑ _j : Fin P.count, (2 * sqrt M / sqrt s) * ‖d‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm j)) (by positivity)
    _ = (K / (ell / 2)) * ((P.count : ℝ) * ((2 * sqrt M / sqrt s) * ‖d‖ ^ 2)) := by simp
    _ ≤ (K / (ell / 2)) * ((n : ℝ) * ((2 * sqrt M / sqrt s) * ‖d‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast P.count_le
    _ = _ := by ring

end SHE.AllAgeMeanEnergy
