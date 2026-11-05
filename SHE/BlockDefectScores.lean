module

public import SHE.BlockPointScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Actual clipped defect rows for separated stopping-age blocks, retaining
all original target heat ages and normalizing by the full weighted history. -/
namespace SHE.BlockDefectScores
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatHistoryScore HeatTorus HeatTorusKernel
  HeatProjection GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks
  StoppedBlockMean RealHeatCovarianceMean MeasurableGaussianScores
  GaussianBlockEvaluation HeatChristoffel RealHeatScore RealHeatEnergyScore BlockPointScores
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {g n : ℕ}

theorem realDefect_basis (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i-u = 4*π^2*t i) (hact : ∀ i, u<σ i) (i : Fin n) :
    (realDefect σ target a u Λ t hage hact (EuclideanSpace.basisFun (Fin n) ℝ i) : HeatTorus.CircleL2) =
      (1-(exp (-Λ*(σ i-u)):ℂ)) • unitHeatKernel (t i) (a i) := by
  change ((realCurrent σ target a u t hage hact (EuclideanSpace.basisFun (Fin n) ℝ i) : HeatTorus.CircleL2) -
    (realDamped σ target a u Λ t hage hact (EuclideanSpace.basisFun (Fin n) ℝ i) : HeatTorus.CircleL2)) = _
  rw [realCurrent_basis, StoppedCanonicalScore.realDamped_basis, sub_smul, one_smul]

def defectBlockRow (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i-u=4*π^2*t i)
    (hact : ∀ j i, u<groupData label rep σ j i) (j : Fin g) :
    State n →ₗ[ℝ] heatSpan (groupData label rep t j) (groupData label rep a j) :=
  (realDefect (groupData label rep σ j) (groupData label rep target j) (groupData label rep a j)
    u Λ (groupData label rep t j) (fun i => by unfold groupData; split_ifs <;> exact hage _) (hact j)).comp
    (restrictCoefficients label j)

theorem defectBlockRow_basis (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i-u=4*π^2*t i)
    (hact : ∀ j i, u<groupData label rep σ j i) (j : Fin g) (i : Fin n) :
    (defectBlockRow label rep σ target a u Λ t hage hact j (EuclideanSpace.basisFun (Fin n) ℝ i) : HeatTorus.CircleL2) =
      if label i=j then (1-(exp (-Λ*(σ i-u)):ℂ)) • unitHeatKernel (t i) (a i) else 0 := by
  unfold defectBlockRow
  rw [LinearMap.comp_apply, restrictCoefficients_basis]
  by_cases hi : label i=j
  · rw [ite_eq_left hi, ite_eq_left hi, realDefect_basis]
    simp only [groupData, hi, ite_true]
  · rw [ite_eq_right hi, ite_eq_right hi, map_zero, Submodule.coe_zero]

theorem defectBlockRow_sum (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ)
    (t : Fin n → ℝ) (hage : ∀ i, target i-u=4*π^2*t i)
    (hact : ∀ j i, u<groupData label rep σ j i) (hact0 : ∀ i, u<σ i) (z : State n) :
    (∑ j, (defectBlockRow label rep σ target a u Λ t hage hact j z : HeatTorus.CircleL2)) =
      (realDefect σ target a u Λ t hage hact0 z : HeatTorus.CircleL2) := by
  let S : State n →ₗ[ℝ] HeatTorus.CircleL2 := ∑ j,
    ((heatSpan (groupData label rep t j) (groupData label rep a j)).subtype.restrictScalars ℝ).comp
      (defectBlockRow label rep σ target a u Λ t hage hact j)
  let S0 : State n →ₗ[ℝ] HeatTorus.CircleL2 := ((heatSpan t a).subtype.restrictScalars ℝ).comp
    (realDefect σ target a u Λ t hage hact0)
  have he : S=S0 := by
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    change S (EuclideanSpace.basisFun (Fin n) ℝ i) = S0 (EuclideanSpace.basisFun (Fin n) ℝ i)
    simp only [S, S0, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply]
    rw [Finset.sum_eq_single (label i)]
    · rw [defectBlockRow_basis, ite_eq_left rfl, realDefect_basis]
    · intro j _ hji; rw [defectBlockRow_basis, ite_eq_right (Ne.symm hji)]
    · simp
  simpa only [S, S0, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Submodule.subtype_apply] using congrArg (fun L : State n →ₗ[ℝ] HeatTorus.CircleL2 => L z) he

theorem defectBlockRow_energy (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (a : Fin n → UnitAddCircle) (u Λ : ℝ) (hΛ : 0<Λ)
    (t : Fin n → ℝ) (hage : ∀ i, target i-u=4*π^2*t i) (hages : ∀ i, σ i≤target i)
    (hact : ∀ j i, u<groupData label rep σ j i) (j : Fin g)
    (w M : ℝ) (hw : 0<w) (hM : 1≤M)
    (hlo : ∀ i, u+w≤groupData label rep σ j i) (hhi : ∀ i, groupData label rep σ j i≤u+M*w)
    (z : State n) :
    ‖defectBlockRow label rep σ target a u Λ t hage hact j z‖ ^ 2 ≤
      (max M 8 * min 1 (Λ*w)^2 * w⁻¹) *
        ‖StoppedAgeBlocks.blockSynthesis label rep σ target (nativeCenter a) hages u j z‖ ^ 2 := by
  have he := stopped_current_difference_clipped Finset.univ
    (fun i => ((restrictCoefficients label j z) i:ℂ)) (groupData label rep σ j)
    (groupData label rep target j) (nativeCenter (groupData label rep a j))
    (fun i _=>groupData_ages label rep σ target hages j i) hΛ hw hM (fun i _=>hlo i) (fun i _=>hhi i)
  have hcenter : nativeCenter (groupData label rep a j)=groupData label rep (nativeCenter a) j := by
    funext i; unfold nativeCenter groupData; split_ifs <;> rfl
  rw [StoppedAgeBlocks.blockSynthesis_norm_sq]
  change ‖realDefect (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep a j) u Λ (groupData label rep t j) _ _ (restrictCoefficients label j z)‖^2 ≤ _
  rw [realDefect_norm_sq, hcenter]
  rw [hcenter] at he
  exact he

end SHE.BlockDefectScores
