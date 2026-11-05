module

public import SHE.StoppedBlockMean

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The actual canonical full-covariance mean energy obtained from physical
separated stopping-age blocks and collision-uniform target heat spans. -/
namespace SHE.StoppedBlockEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks
  StoppedBlockMean RealHeatCovarianceMean MeasurableGaussianScores BlockMeanEnergy
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem translated_physical_block_mean_energy (n : ℕ) :
    ∃ h K θ : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧ 0 < θ ∧
      ∀ {g : ℕ}, 0 < g → ∀ (label : Fin n → Fin g) (rep : Fin g → Fin n),
      ∀ (hrep : ∀ j, label (rep j) = j),
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ), (∀ i, 0 < t i) → (∀ i, t i ≤ h) →
      ∀ (hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (hages : ∀ i, σ i ≤ target i)
      (lower upper : Fin g → ℝ) (A : ℝ), 4 * (g : ℝ) ^ 2 + 1 ≤ A →
      ∀ (hlo : ∀ j, 0 < lower j), (∀ j, lower j ≤ upper j) →
      ∀ (hstlo : ∀ i, u + lower (label i) ≤ σ i) (hsthi : ∀ i, σ i ≤ u + upper (label i)),
      (∀ j k, j < k → A * upper j ≤ lower k) →
      ∀ (w M : Fin g → ℝ), (∀ j, 0 < w j) → (∀ j, 1 ≤ M j) →
      (∀ i, w (label i) ≤ t i) → (∀ i, t i ≤ M (label i) * w (label i)) →
      ∀ (c : UnitAddCircle × Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
      (hcb : ∀ x p, 0 ≤ c (x,p) ∧ c (x,p) ≤ U), 0 < ell → (∀ x p, ell ≤ c (x,p)) →
      ∀ d : HeatTorus.CircleL2,
      let act : ∀ j i, u < groupData label rep σ j i := fun j i => by
        have hb := (groupData_bounds label rep hrep σ
          (fun j => u + lower j) (fun j => u + upper j) hstlo hsthi j i).1
        linarith [hlo j]
      let S := fun j x => blockMean label rep σ target (fun i => a i + x) u Λ t hage act j
      let V := fun x => StoppedGaussianFeatures.stoppedCovariance σ target
        (nativeCenter (fun i => a i + x)) (fun p => c (x,p)) u
      Integrable (fun x => scoreVariance (V x) (meanDirection (∑ j, S j x) d)) haarAddCircle ∧
      (∫ x, scoreVariance (V x) (meanDirection (∑ j, S j x) d) ∂haarAddCircle) ≤
        (K / (ell / 2)) * ∑ j, (2 / lower j) * sqrt (M j) * sqrt (w j) *
          ‖CircleHeat.heat (θ * w j) d‖ ^ 2 := by
  obtain ⟨h, K, θ, hh, hh1, hK, hθ, hb⟩ := translated_block_scoreVariance_bound n
  refine ⟨h, K, θ, hh, hh1, hK, hθ, ?_⟩
  intro g hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper A hA hlo hlohi hstlo hsthi hsep
    w M hw hM htwlo htwhi c hc U ell hcb hell hcl d
  let act : ∀ j i, u < groupData label rep σ j i := fun j i => by
    have hgi := (groupData_bounds label rep hrep σ (fun j => u + lower j)
      (fun j => u + upper j) hstlo hsthi j i).1
    linarith [hlo j]
  let v := fun x => weightedFeature σ target (nativeCenter (fun i => a i + x))
    (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u
  let C := fun j x => StoppedAgeBlocks.blockSynthesis label rep σ target
    (nativeCenter (fun i => a i + x)) hages u j
  let S := fun j x => blockMean label rep σ target (fun i => a i + x) u Λ t hage act j
  have htl (j : Fin g) (i : Fin n) : w j ≤ groupData label rep t j i ∧
      groupData label rep t j i ≤ M j * w j :=
    groupData_bounds label rep hrep t w (fun j => M j * w j) htwlo htwhi j i
  have htj (j : Fin g) (i : Fin n) : 0 < groupData label rep t j i := (hw j).trans_le (htl j i).1
  have hthj (j : Fin g) (i : Fin n) : groupData label rep t j i ≤ h := by
    unfold groupData; split_ifs <;> exact hth _
  have hspan (j : Fin g) (x : UnitAddCircle) (z : State n) :
      S j x z ∈ heatSpan (groupData label rep t j) (fun i => groupData label rep a j i + x) := by
    have hs := blockMean_span label rep σ target (fun i => a i + x) u Λ t hage act j z
    have ha : groupData label rep (fun i => a i + x) j = fun i => groupData label rep a j i + x := by
      funext i; unfold groupData; split_ifs <;> rfl
    simpa only [ha] using hs
  have hrow (j : Fin g) (x : UnitAddCircle) (z : State n) :
      ‖S j x z‖ ≤ sqrt (2 / lower j) * ‖C j x z‖ := by
    exact blockMean_row_bound label rep σ target (fun i => a i + x) u Λ hΛ t hage hages act j
      (lower j) (hlo j) (fun i => (groupData_bounds label rep hrep σ
        (fun j => u + lower j) (fun j => u + upper j) hstlo hsthi j i).1) z
  have hframe (x : UnitAddCircle) (z : State n) :
      (ell / 2) * (∑ j, ‖C j x z‖ ^ 2) ≤ ‖featureSynthesis (v x) z‖ ^ 2 :=
    weighted_block_frame hg label rep hrep σ target (nativeCenter (fun i => a i + x)) hages u
      lower upper A hA hlo hlohi hstlo hsthi hsep (fun p => c (x,p))
      (hc.comp (measurable_const.prodMk measurable_id)) U ell (hcb x) hell.le (hcl x) z
  have he := hb (fun j => groupData label rep t j) (fun j => groupData label rep a j) htj hthj
    w M hw hM (fun j i => (htl j i).1) (fun j i => (htl j i).2) v C S
    (translated_feature_gram_measurable σ target a hages u hc U hcb)
    (fun j i => blockMean_translated_basis_measurable label rep σ target a u Λ t ht hage act j i)
    (fun j => sqrt (2 / lower j)) (ell / 2) (fun _ => sqrt_nonneg _) (half_pos hell)
    hspan hrow hframe d
  have hgram (x : UnitAddCircle) := weightedFeature_gram σ target (nativeCenter (fun i => a i + x))
    (fun p => c (x,p)) (hc.comp (measurable_const.prodMk measurable_id)) U (hcb x) hages u
  change ∀ x, Matrix.gram ℝ (v x) = _ at hgram
  simp_rw [hgram] at he
  have hs (j : Fin g) : sqrt (2 / lower j) ^ 2 = 2 / lower j :=
    sq_sqrt (div_nonneg (by norm_num) (hlo j).le)
  simp_rw [hs] at he
  exact he

end SHE.StoppedBlockEnergy
