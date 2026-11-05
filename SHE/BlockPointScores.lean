module

public import SHE.GaussianBlockEvaluation
public import SHE.StoppedBlockEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Physical finite-block point scores. A.e. continuous evaluation of all
block rows is identified with evaluation of their genuine L2 sum. -/
namespace SHE.BlockPointScores
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks
  StoppedBlockMean RealHeatCovarianceMean MeasurableGaussianScores
  GaussianBlockEvaluation HeatChristoffel RealHeatScore RealHeatEnergyScore
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {g n q : ℕ}

/-- Different finite heat-span continuous evaluations agree a.e. with the
actual L2 sum; there is no compatibility assumption on chosen lifts. -/
theorem evaluationDirection_sum_ae
    (t : Fin g → Fin q → ℝ) (a : Fin g → Fin q → UnitAddCircle) (ht : ∀ j i, 0 < t j i)
    (S : ∀ j, State n →ₗ[ℝ] heatSpan (t j) (a j))
    (t0 : Fin n → ℝ) (a0 : Fin n → UnitAddCircle) (ht0 : ∀ i, 0 < t0 i)
    (S0 : State n →ₗ[ℝ] heatSpan t0 a0)
    (hsum : ∀ z, (∑ j, (S j z : HeatTorus.CircleL2)) = (S0 z : HeatTorus.CircleL2)) :
    (fun x => ∑ j, evaluationDirection (t j) (a j) (ht j) (S j) x) =ᵐ[haarAddCircle]
      (fun x => evaluationDirection t0 a0 ht0 S0 x) := by
  have hj (j : Fin g) (i : Fin n) := evaluation_ae (t j) (a j) (ht j)
    (S j (EuclideanSpace.basisFun (Fin n) ℝ i))
  have h0 (i : Fin n) := evaluation_ae t0 a0 ht0 (S0 (EuclideanSpace.basisFun (Fin n) ℝ i))
  have hLp (i : Fin n) := Lp.coeFn_fun_finsetSum Finset.univ
    (fun j => (S j (EuclideanSpace.basisFun (Fin n) ℝ i) : HeatTorus.CircleL2))
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hj j)), ae_all_iff.mpr h0,
    ae_all_iff.mpr hLp] with x hx hx0 hxLp
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext i
  change (∑ j, evaluationDirection (t j) (a j) (ht j) (S j) x) i =
    evaluationDirection t0 a0 ht0 S0 x i
  simp only [WithLp.ofLp_sum, Finset.sum_apply, evaluationDirection_apply, realEvaluation_apply]
  simp_rw [hx]
  rw [← Complex.re_sum, hx0 i]
  have hh := hxLp i
  rw [hsum] at hh
  exact congrArg Complex.re hh.symm

def dampedBlockRow (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (j : Fin g) :
    State n →ₗ[ℝ] heatSpan (groupData label rep t j) (groupData label rep a j) :=
  (realDamped (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep a j) u Λ (groupData label rep t j)
    (fun i => by unfold groupData; split_ifs <;> exact hage _) (hactive j)).comp
    (restrictCoefficients label j)

theorem dampedBlockRow_sum (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (hact : ∀ i, u < σ i) (z : State n) :
    (∑ j, (dampedBlockRow label rep σ target a u Λ t hage hactive j z : HeatTorus.CircleL2)) =
      (realDamped σ target a u Λ t hage hact z : HeatTorus.CircleL2) := by
  have hs := congrArg (fun L : State n →ₗ[ℝ] HeatTorus.CircleL2 => L z)
    (blockMean_sum label rep σ target a u Λ t hage hactive hact)
  convert! (by simpa only [LinearMap.sum_apply] using hs) using 1

/-- Actual canonical damped point scores against the original weighted full
stopped covariance, with each block's genuine stopping denominator. -/
theorem damped_block_point_score (n : ℕ) :
    ∃ h K : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < K ∧
      ∀ {g : ℕ}, 0 < g → ∀ (label : Fin n → Fin g) (rep : Fin g → Fin n)
      (_hrep : ∀ j, label (rep j) = j),
      ∀ (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ), 0 < Λ →
      ∀ (t : Fin n → ℝ) (_ht : ∀ i, 0 < t i), (∀ i, t i ≤ h) →
      ∀ (_hage : ∀ i, target i - u = 4 * π ^ 2 * t i) (_hages : ∀ i, σ i ≤ target i)
      (lower upper : Fin g → ℝ) (A : ℝ), 4 * (g : ℝ) ^ 2 + 1 ≤ A →
      (∀ j, 0 < lower j) → (∀ j, lower j ≤ upper j) →
      (∀ i, u + lower (label i) ≤ σ i) → (∀ i, σ i ≤ u + upper (label i)) →
      (∀ j k, j < k → A * upper j ≤ lower k) →
      ∀ (c : Domain → ℝ) (_hc : Measurable c) (U ell : ℝ)
      (_hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U), 0 < ell → (∀ p, ell ≤ c p) →
      ∀ᵐ x ∂haarAddCircle,
      let V := StoppedGaussianFeatures.stoppedCovariance σ target (nativeCenter a) c u
      let d := physicalDampedDirection σ target a u Λ x
      d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) V).range ∧
      scoreVariance V d ≤ (K / (ell / 2)) * ∑ j, (2 / lower j) *
        ∑ i, GlobalTorusHeatSpan.weight (groupData label rep t j i) (groupData label rep a j i) x := by
  obtain ⟨h, K, hh, hh1, hK, hb⟩ := block_evaluation_scoreVariance_bound n
  refine ⟨h, K, hh, hh1, hK, ?_⟩
  intro g hg label rep hrep σ target a u Λ hΛ t ht hth hage hages lower upper A hA hlo hlohi hstlo hsthi hsep
    c hc U ell hcb hell hcl
  let act : ∀ j i, u < groupData label rep σ j i := fun j i => by
    have hp := (groupData_bounds label rep hrep σ (fun j => u + lower j)
      (fun j => u + upper j) hstlo hsthi j i).1
    linarith [hlo j]
  let act0 : ∀ i, u < σ i := fun i => by linarith [hstlo i, hlo (label i)]
  let v := weightedFeature σ target (nativeCenter a) c hc U hcb hages u
  let C := StoppedAgeBlocks.blockSynthesis label rep σ target (nativeCenter a) hages u
  let S := dampedBlockRow label rep σ target a u Λ t hage act
  have htj (j : Fin g) (i : Fin n) : 0 < groupData label rep t j i := by
    unfold groupData; split_ifs <;> exact ht _
  have hthj (j : Fin g) (i : Fin n) : groupData label rep t j i ≤ h := by
    unfold groupData; split_ifs <;> exact hth _
  have hrow (j : Fin g) (z : State n) :
      (lower j / 2) * ‖S j z‖ ^ 2 ≤ ‖C j z‖ ^ 2 := by
    have he := blockMean_row_bound label rep σ target a u Λ hΛ t hage hages act j
      (lower j) (hlo j) (fun i => (groupData_bounds label rep hrep σ
        (fun j => u + lower j) (fun j => u + upper j) hstlo hsthi j i).1) z
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mpr he
    rw [mul_pow, sq_sqrt (div_nonneg (by norm_num) (hlo j).le)] at hs
    change ‖S j z‖ ^ 2 ≤ (2 / lower j) * ‖C j z‖ ^ 2 at hs
    calc
      _ ≤ (lower j / 2) * ((2 / lower j) * ‖C j z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hs (half_pos (hlo j)).le
      _ = _ := by field_simp [(hlo j).ne']
  have hframe (z : State n) : (ell / 2) * (∑ j, ‖C j z‖ ^ 2) ≤ ‖featureSynthesis v z‖ ^ 2 :=
    weighted_block_frame hg label rep hrep σ target (nativeCenter a) hages u lower upper A
      hA hlo hlohi hstlo hsthi hsep c hc U ell hcb hell.le hcl z
  let dir := fun x => ∑ j, evaluationDirection (groupData label rep t j) (groupData label rep a j)
    (htj j) (S j) x
  have hpt (x : UnitAddCircle) := hb (fun j => groupData label rep t j)
    (fun j => groupData label rep a j) htj hthj v C S (fun j => lower j / 2) (ell / 2)
    (fun j => half_pos (hlo j)) (half_pos hell) hrow hframe x (dir x) (fun z => by
      dsimp only [dir]
      rw [inner_sum]
      exact Finset.sum_congr rfl (fun j _ => inner_evaluationDirection _ _ _ _ _ z))
  have he := evaluationDirection_sum_ae (fun j => groupData label rep t j)
    (fun j => groupData label rep a j) htj S t a ht (realDamped σ target a u Λ t hage act0)
    (dampedBlockRow_sum label rep σ target a u Λ t hage act act0)
  have hp := evaluationDirection_damped_ae σ target a u Λ t ht hage act0
  change (fun x => evaluationDirection t a ht (realDamped σ target a u Λ t hage act0) x) =ᵐ[haarAddCircle]
    (physicalDampedDirection σ target a u Λ) at hp
  filter_upwards [he.trans hp] with x hx
  have hgram := weightedFeature_gram σ target (nativeCenter a) c hc U hcb hages u
  have hs := hpt x
  change dir x = _ at hx
  rw [hx, hgram] at hs
  have hinv (j : Fin g) : (lower j / 2)⁻¹ = 2 / lower j := by field_simp
  simp_rw [hinv] at hs
  exact hs

end SHE.BlockPointScores
