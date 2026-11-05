module

public import SHE.StoppedAgeBlocks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Actual all-age mean energy under an explicit finite age partition.
Stopping-age separation and target-age comparability remain distinct. -/
namespace SHE.StoppedBlockMean
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks
  RealHeatCovarianceMean MeasurableGaussianScores BlockMeanEnergy
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {g n : ℕ}

def blockMean (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (j : Fin g) :
    State n →ₗ[ℝ] HeatTorus.CircleL2 :=
  (dampedSynthesis (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep a j) u Λ (groupData label rep t j)
    (fun i => by unfold groupData; split_ifs <;> exact hage _) (hactive j)).comp
    (restrictCoefficients label j)

theorem blockMean_span (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (j : Fin g) (z : State n) :
    blockMean label rep σ target a u Λ t hage hactive j z ∈
      heatSpan (groupData label rep t j) (groupData label rep a j) :=
  (realDamped (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep a j) u Λ (groupData label rep t j)
    (fun i => by unfold groupData; split_ifs <;> exact hage _) (hactive j)
    (restrictCoefficients label j z)).property

theorem blockMean_basis (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (j : Fin g) (i : Fin n) :
    blockMean label rep σ target a u Λ t hage hactive j (EuclideanSpace.basisFun (Fin n) ℝ i) =
      if label i = j then (exp (-Λ * (σ i - u)) : ℂ) • unitHeatKernel (t i) (a i) else 0 := by
  unfold blockMean
  rw [LinearMap.comp_apply, restrictCoefficients_basis]
  by_cases hi : label i = j
  · rw [ite_eq_left hi, ite_eq_left hi, dampedSynthesis_basis]
    simp only [groupData, hi, ite_true]
  · rw [ite_eq_right hi, ite_eq_right hi, map_zero]

/-- Summing the padded blocks recovers the literal full physical damped
mean synthesis, not a replacement family of observations. -/
theorem blockMean_sum (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (hact : ∀ i, u < σ i) :
    (∑ j, blockMean label rep σ target a u Λ t hage hactive j) =
      dampedSynthesis σ target a u Λ t hage hact := by
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro i
  change (∑ j, blockMean label rep σ target a u Λ t hage hactive j)
      (EuclideanSpace.basisFun (Fin n) ℝ i) =
    dampedSynthesis σ target a u Λ t hage hact (EuclideanSpace.basisFun (Fin n) ℝ i)
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (label i)]
  · rw [blockMean_basis, ite_eq_left rfl, dampedSynthesis_basis]
  · intro j _ hji
    rw [blockMean_basis, ite_eq_right (Ne.symm hji)]
  · simp

theorem blockMean_translated_basis_measurable
    (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hactive : ∀ j i, u < groupData label rep σ j i) (j : Fin g) (i : Fin n) :
    StronglyMeasurable (fun x => blockMean label rep σ target (fun k => a k + x) u Λ t hage hactive j
      (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  have htj : ∀ k, 0 < groupData label rep t j k := by
    intro k; unfold groupData; split_ifs <;> exact ht _
  have hm := translated_basis_stronglyMeasurable (groupData label rep σ j)
    (groupData label rep target j) (groupData label rep a j) u Λ (groupData label rep t j) htj
    (fun k => by unfold groupData; split_ifs <;> exact hage _) (hactive j) i
  by_cases hi : label i = j
  · convert! hm using 1
    funext x
    unfold blockMean
    rw [LinearMap.comp_apply, restrictCoefficients_basis, ite_eq_left hi]
    have ha : groupData label rep (fun k => a k + x) j =
        fun k => groupData label rep a j k + x := by
      funext k; unfold groupData; split_ifs <;> rfl
    rw [ha]
  · have hz : (fun x => blockMean label rep σ target (fun k => a k + x) u Λ t hage hactive j
        (EuclideanSpace.basisFun (Fin n) ℝ i)) = fun _ => 0 := by
      funext x
      unfold blockMean
      rw [LinearMap.comp_apply, restrictCoefficients_basis, ite_eq_right hi, map_zero]
    rw [hz]
    exact stronglyMeasurable_const

theorem blockMean_row_bound
    (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ) (hΛ : 0 < Λ)
    (t : Fin n → ℝ) (hage : ∀ i, target i - u = 4 * π ^ 2 * t i)
    (hages : ∀ i, σ i ≤ target i) (hactive : ∀ j i, u < groupData label rep σ j i)
    (j : Fin g) (δ : ℝ) (hδ : 0 < δ) (hstop : ∀ i, u + δ ≤ groupData label rep σ j i)
    (z : State n) :
    ‖blockMean label rep σ target a u Λ t hage hactive j z‖ ≤
      sqrt (2 / δ) * ‖StoppedAgeBlocks.blockSynthesis label rep σ target (nativeCenter a) hages u j z‖ := by
  have hh := stopped_damped_current_row_bound Finset.univ
    (fun i => ((restrictCoefficients label j z) i : ℂ))
    (groupData label rep σ j) (groupData label rep target j) (nativeCenter (groupData label rep a j))
    (fun i _ => groupData_ages label rep σ target hages j i) hΛ hδ (fun i _ => hstop i)
  have hcenter : nativeCenter (groupData label rep a j) = groupData label rep (nativeCenter a) j := by
    funext i
    unfold nativeCenter groupData
    split_ifs <;> rfl
  rw [hcenter] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, sq_sqrt (by positivity : 0 ≤ 2 / δ), StoppedAgeBlocks.blockSynthesis_norm_sq]
  convert! hh using 1
  have he := realDamped_norm_sq (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep a j) u Λ (groupData label rep t j)
    (fun i => by unfold groupData; split_ifs <;> exact hage _) (hactive j)
    (restrictCoefficients label j z)
  rw [hcenter] at he
  exact he

end SHE.StoppedBlockMean
