module

public import SHE.BlockDefectScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Canonical physical clipped defect scores against the full individually
stopped covariance, obtained from genuine separated-history age blocks. -/
namespace SHE.StoppedBlockDefectEnergy
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks
  StoppedBlockMean RealHeatCovarianceMean MeasurableGaussianScores
  GaussianBlockEvaluation HeatChristoffel RealHeatScore RealHeatEnergyScore BlockPointScores BlockDefectScores
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem clipped_block_point_score (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ {g : ℕ}, 0 < g → ∀ (label : Fin n → Fin g) (rep : Fin g → Fin n)
      (_hrep : ∀ j, label (rep j) = j),
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (_ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (_hage : ∀ i, target i-u=4*π^2*t i) (_hages : ∀ i, σ i≤target i)
      (lower upper M : Fin g → ℝ) (A : ℝ), 4*(g:ℝ)^2+1≤A →
      (∀ j, 0<lower j) → (∀ j, lower j≤upper j) → (∀ j, 1≤M j) →
      (∀ j, upper j≤M j*lower j) →
      (∀ i, u+lower (label i)≤σ i) → (∀ i, σ i≤u+upper (label i)) →
      (∀ j k, j<k → A*upper j≤lower k) →
      ∀ (c : Domain → ℝ) (_hc : Measurable c) (U ell : ℝ)
      (_hcb : ∀ p, 0≤c p ∧ c p≤U), 0<ell → (∀ p, ell≤c p) →
      ∀ᵐ x ∂haarAddCircle,
      let V := StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) c u
      let d := physicalDefectDirection σ target a u Λ x
      d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) V).range ∧
      scoreVariance V d ≤ (K/(ell/2)) * ∑ j,
        (max (M j) 8 * min 1 (Λ*lower j)^2 * (lower j)⁻¹) *
          ∑ i, GlobalTorusHeatSpan.weight (groupData label rep t j i) (groupData label rep a j i) x := by
  obtain ⟨h, K, hh, hh1, hK, hb⟩ := block_energy_scoreVariance_bound n
  refine ⟨h,K,hh,hh1,hK,?_⟩
  intro g hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper M A hA hlo hlohi hM hratio
    hstlo hsthi hsep c hc U ell hcb hell hcl
  let act : ∀ j i, u<groupData label rep σ j i := fun j i => by
    have hp := (groupData_bounds label rep hrep σ (fun j=>u+lower j)
      (fun j=>u+upper j) hstlo hsthi j i).1
    linarith [hlo j]
  let act0 : ∀ i, u<σ i := fun i=>by linarith [hstlo i,hlo (label i)]
  let v := weightedFeature σ target (nativeCenter a) c hc U hcb hages u
  let C := StoppedAgeBlocks.blockSynthesis label rep σ target (nativeCenter a) hages u
  let S := defectBlockRow label rep σ target a u Λ t hage act
  let E := fun j => max (M j) 8 * min 1 (Λ*lower j)^2 * (lower j)⁻¹
  have hE (j : Fin g) : 0≤E j := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) (sq_nonneg _))
      (inv_nonneg.mpr (hlo j).le)
  have htj (j : Fin g) (i : Fin n) : 0<groupData label rep t j i := by
    unfold groupData; split_ifs <;> exact ht _
  have hthj (j : Fin g) (i : Fin n) : groupData label rep t j i≤h := by
    unfold groupData; split_ifs <;> exact hth _
  have hrow (j : Fin g) (z : State n) : ‖S j z‖^2≤sqrt (E j)^2*‖C j z‖^2 := by
    rw [sq_sqrt (hE j)]
    apply defectBlockRow_energy label rep σ target a u Λ hΛ t hage hages act j
      (lower j) (M j) (hlo j) (hM j) _ _ z
    · intro i
      exact (groupData_bounds label rep hrep σ (fun j=>u+lower j)
        (fun j=>u+upper j) hstlo hsthi j i).1
    · intro i
      have hp := (groupData_bounds label rep hrep σ (fun j=>u+lower j)
        (fun j=>u+upper j) hstlo hsthi j i).2
      linarith [hratio j]
  have hframe (z : State n) : (ell/2)*(∑ j,‖C j z‖^2)≤‖featureSynthesis v z‖^2 :=
    weighted_block_frame hg label rep hrep σ target (nativeCenter a) hages u lower upper A
      hA hlo hlohi hstlo hsthi hsep c hc U ell hcb hell.le hcl z
  let dir := fun x=>∑ j,evaluationDirection (groupData label rep t j) (groupData label rep a j)
    (htj j) (S j) x
  have hpt (x : UnitAddCircle) := hb (fun j=>groupData label rep t j)
    (fun j=>groupData label rep a j) htj hthj v C S (fun j=>sqrt (E j)) (ell/2)
    (fun _=>sqrt_nonneg _) (half_pos hell) hrow hframe x (dir x) (fun z=>by
      dsimp only [dir]
      rw [inner_sum]
      exact Finset.sum_congr rfl (fun j _=>inner_evaluationDirection _ _ _ _ _ z))
  have he := evaluationDirection_sum_ae (fun j=>groupData label rep t j)
    (fun j=>groupData label rep a j) htj S t a ht (realDefect σ target a u Λ t hage act0)
    (defectBlockRow_sum label rep σ target a u Λ t hage act act0)
  have hp := evaluationDirection_defect_ae σ target a u Λ t ht hage act0
  filter_upwards [he.trans hp] with x hx
  have hs := hpt x
  change dir x=_ at hx
  rw [hx,weightedFeature_gram] at hs
  have heq (j : Fin g) : sqrt (E j)^2=E j := sq_sqrt (hE j)
  simp_rw [heq] at hs
  exact hs

end SHE.StoppedBlockDefectEnergy
