module

public import SHE.StoppedMeanEnergy
public import SHE.BlockMeanEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Literal finite age blocks of individually stopped histories. Padding a
block repeats one original observation and gives it zero coefficient, so all
physical targets and stopping indicators of active entries remain unchanged.
The all-age real covariance frame is derived from physical history separation. -/
namespace SHE.StoppedAgeBlocks
open Set MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  GaussianGramScore GaussianIncrement StoppedMeanEnergy HeatTorus
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {g n : ℕ}

def restrictCoefficients (label : Fin n → Fin g) (j : Fin g) : State n →ₗ[ℝ] State n where
  toFun z := WithLp.toLp 2 (fun i => if label i = j then z i else 0)
  map_add' z w := by
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    funext i
    change (if label i = j then z i + w i else 0) =
      (if label i = j then z i else 0) + (if label i = j then w i else 0)
    split_ifs <;> simp
  map_smul' a z := by
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    funext i
    change (if label i = j then a * z i else 0) = a * (if label i = j then z i else 0)
    split_ifs <;> simp

def groupData {E : Type*} (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (v : Fin n → E) (j : Fin g) (i : Fin n) : E :=
  if label i = j then v i else v (rep j)

theorem restrictCoefficients_apply (label : Fin n → Fin g) (j : Fin g) (z : State n) (i : Fin n) :
    restrictCoefficients label j z i = if label i = j then z i else 0 := rfl

theorem restrictCoefficients_basis (label : Fin n → Fin g) (j : Fin g) (i : Fin n) :
    restrictCoefficients label j (EuclideanSpace.basisFun (Fin n) ℝ i) =
      if label i = j then EuclideanSpace.basisFun (Fin n) ℝ i else 0 := by
  apply (WithLp.equiv 2 (Fin n → ℝ)).injective
  funext k
  by_cases hi : label i = j
  · simp only [hi, ite_true]
    change restrictCoefficients label j (EuclideanSpace.basisFun (Fin n) ℝ i) k =
      (EuclideanSpace.basisFun (Fin n) ℝ i) k
    rw [restrictCoefficients_apply]
    by_cases hki : k = i
    · subst k; simp only [hi, ite_true]
    · simp [EuclideanSpace.basisFun_apply, hki]
  · simp only [hi, ite_false]
    change restrictCoefficients label j (EuclideanSpace.basisFun (Fin n) ℝ i) k = (0 : State n) k
    rw [restrictCoefficients_apply]
    by_cases hki : k = i
    · subst k; simp only [hi, ite_false, PiLp.zero_apply]
    · simp [EuclideanSpace.basisFun_apply, hki]

theorem groupData_bounds {E : Type*} [Preorder E] (label : Fin n → Fin g)
    (rep : Fin g → Fin n) (hrep : ∀ j, label (rep j) = j) (v : Fin n → E)
    (lo hi : Fin g → E) (hlo : ∀ i, lo (label i) ≤ v i) (hhi : ∀ i, v i ≤ hi (label i))
    (j : Fin g) (i : Fin n) : lo j ≤ groupData label rep v j i ∧ groupData label rep v j i ≤ hi j := by
  unfold groupData
  split_ifs with h
  · simpa only [h] using And.intro (hlo i) (hhi i)
  · simpa only [hrep j] using And.intro (hlo (rep j)) (hhi (rep j))

theorem groupData_ages (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (hages : ∀ i, σ i ≤ target i) (j : Fin g) (i : Fin n) :
    groupData label rep σ j i ≤ groupData label rep target j i := by
  unfold groupData
  split_ifs <;> exact hages _

theorem historyF_group_sum (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (z : State n) :
    (fun u => ∑ j, historyF Finset.univ
      (fun i => ((restrictCoefficients label j z) i : ℂ))
      (groupData label rep σ j) (groupData label rep target j) (groupData label rep center j) u) =
      historyF Finset.univ (fun i => (z i : ℂ)) σ target center := by
  funext u
  unfold historyF
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (label i)]
  · simp only [groupData, ite_true, restrictCoefficients_apply]
  · intro j _ hji
    have hij : label i ≠ j := Ne.symm hji
    simp only [restrictCoefficients_apply, ite_eq_right hij, Complex.ofReal_zero, zero_smul, ite_self]
  · simp

/-- The actual unweighted real block synthesis, with inactive padded
coordinates suppressed before physical history formation. -/
def blockSynthesis (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (j : Fin g) :
    State n →ₗ[ℝ] Lp ℝ 2 (historyMeasure q) :=
  (featureSynthesis (weightedFeature (groupData label rep σ j) (groupData label rep target j)
    (groupData label rep center j) (fun _ => 1) measurable_const 1 (fun _ => ⟨by norm_num, le_rfl⟩)
    (groupData_ages label rep σ target hages j) q)).comp (restrictCoefficients label j)

theorem blockSynthesis_norm_sq (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (j : Fin g) (z : State n) :
    ‖blockSynthesis label rep σ target center hages q j z‖ ^ 2 =
      (fullPhysicalEnergy (historyF Finset.univ
        (fun i => ((restrictCoefficients label j z) i : ℂ))
        (groupData label rep σ j) (groupData label rep target j) (groupData label rep center j)) q).toReal := by
  have hb := weightedSynthesis_full_history_bounds (groupData label rep σ j)
    (groupData label rep target j) (groupData label rep center j) (fun _ => 1)
    measurable_const 1 (fun _ => ⟨by norm_num, le_rfl⟩)
    (groupData_ages label rep σ target hages j) (fun _ => le_rfl) q
    (restrictCoefficients label j z)
  apply le_antisymm
  · convert! (by simpa only [one_mul] using hb.2) using 1
  · convert! (by simpa only [one_mul] using hb.1) using 1

/-- A genuine weighted full-history real frame for arbitrary finite separated
age blocks. The only separation assumptions concern the original stopping
ages; there is no covariance domination assumption. -/
theorem weighted_block_frame (hg : 0 < g) (label : Fin n → Fin g) (rep : Fin g → Fin n)
    (hrep : ∀ j, label (rep j) = j) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ i, σ i ≤ target i) (q : ℝ) (lower upper : Fin g → ℝ) (A : ℝ)
    (hA : 4 * (g : ℝ) ^ 2 + 1 ≤ A) (hlo : ∀ j, 0 < lower j) (hlohi : ∀ j, lower j ≤ upper j)
    (hstlo : ∀ i, q + lower (label i) ≤ σ i) (hsthi : ∀ i, σ i ≤ q + upper (label i))
    (hsep : ∀ j k, j < k → A * upper j ≤ lower k)
    (c : Domain → ℝ) (hc : Measurable c) (U ell : ℝ)
    (hcb : ∀ p, 0 ≤ c p ∧ c p ≤ U) (hell : 0 ≤ ell) (hcl : ∀ p, ell ≤ c p)
    (z : State n) :
    (ell / 2) * (∑ j, ‖blockSynthesis label rep σ target center hages q j z‖ ^ 2) ≤
      ‖featureSynthesis (weightedFeature σ target center c hc U hcb hages q) z‖ ^ 2 := by
  have hb := separated_history_covariance_frame hg (fun _ => Finset.univ)
    (fun j i => ((restrictCoefficients label j z) i : ℂ))
    (groupData label rep σ) (groupData label rep target) (groupData label rep center)
    (fun j i _ => groupData_ages label rep σ target hages j i) lower upper hA hlo hlohi
    (fun j i _ => (groupData_bounds label rep hrep σ (fun j => q + lower j)
      (fun j => q + upper j) hstlo hsthi j i).1)
    (fun j i _ => (groupData_bounds label rep hrep σ (fun j => q + lower j)
      (fun j => q + upper j) hstlo hsthi j i).2) hsep
  rw [historyF_group_sum] at hb
  have he := (weightedSynthesis_full_history_bounds σ target center c hc U hcb hages hcl q z).1
  simp_rw [blockSynthesis_norm_sq]
  have hm := mul_le_mul_of_nonneg_left hb hell
  have hm' : (ell / 2) * (∑ j, (fullPhysicalEnergy (historyF Finset.univ
      (fun i => ((restrictCoefficients label j z) i : ℂ))
      (groupData label rep σ j) (groupData label rep target j) (groupData label rep center j)) q).toReal) ≤
      ell * (fullPhysicalEnergy (historyF Finset.univ (fun i => (z i : ℂ)) σ target center) q).toReal := by
    convert! hm using 1; ring
  exact hm'.trans he

end SHE.StoppedAgeBlocks
