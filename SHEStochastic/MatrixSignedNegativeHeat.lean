module

public import SHEStochastic.MatrixWeightedOutput
public import SHEStochastic.MatrixColumnComparison
public import SHEStochastic.MatrixJetSegment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHEStochastic.MatrixSignedNegativeHeat
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.CircleHeat SHE.HaarWeightedHeat
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixColumnComparison MatrixProfileInterpolation
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (P Q : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ := 0) : ℝ :=
  MatrixHaarNegativeFamily.constant (blend P Q 0 ⟨le_rfl, zero_le_one⟩) ρ hρ hρhalf k

theorem constant_pos (P Q : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ := 0) :
    0 < constant P Q ρ hρ hρhalf k := MatrixHaarNegativeFamily.constant_pos _ _ _ _ _

def column (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P Q : Profile d) (k : d × HaarNode) : MatrixWeightedOutput.Output d :=
  MatrixWeightedOutput.map Λ ρ t hΛ hρ b B hb
    ((factor Q - factor P) (lp.single 2 k 1))

def jetColumn (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P Q : Profile d) (w : List (Domain (d := d)))
    (k : d × HaarNode) : MatrixWeightedOutput.Output d :=
  MatrixWeightedOutput.map Λ ρ t hΛ hρ b B hb
    (MatrixHaarHigherFamily.jet Q w k - MatrixHaarHigherFamily.jet P w k)

/-- Signed stability of the full infinite adapted matrix factor in a
massive negative norm, after heat and an arbitrary bounded scalar
output multiplier. The right side uses only the signed covariance
profile difference; no absolute-value profile is introduced. -/
theorem jets {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P Q : Profile d)
    (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ) (hM : ∀ q, 0 ≤ M q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q) :
    Summable (fun k => ‖jetColumn Λ ρ t hΛ hρ.le b B hb P Q w k‖^2) ∧
      (∑' k, ‖jetColumn Λ ρ t hΛ hρ.le b B hb P Q w k‖^2) ≤
        constant P Q ρ hρ hρhalf w.length * B^2 * t^(-(1/2 : ℝ)) *
          MatrixNegativeLocalization.energy Λ ρ (difference P Q) * MatrixJetClosure.weight M w^2 := by
  apply MatrixJetSegment.energy P Q w (MatrixWeightedOutput.map Λ ρ t hΛ hρ.le b B hb)
  · have hc := (constant_pos P Q ρ hρ hρhalf w.length).le
    have he := MatrixNegativeLocalization.energy_nonneg (ρ := ρ) hΛ (difference P Q)
    positivity
  · intro s hs
    have hh := MatrixHaarNegativeFamily.energy hΛ hρ hρhalf ht ht1 (blend P Q s hs)
      (difference P Q) w M hM hRest b B hB hb
    have hc : MatrixHaarNegativeFamily.constant (blend P Q s hs) ρ hρ hρhalf w.length = constant P Q ρ hρ hρhalf w.length := rfl
    simpa only [MatrixWeightedOutput.jet_norm_sq, hc] using hh

/-- Signed stability of the full infinite adapted matrix factor in a
massive negative norm, after heat and an arbitrary bounded scalar
output multiplier. The right side uses only the signed covariance
profile difference; no absolute-value profile is introduced. -/
theorem energy {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (b : CircleL2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P Q : Profile d) :
    Summable (fun k => ‖column Λ ρ t hΛ hρ.le b B hb P Q k‖^2) ∧
      (∑' k, ‖column Λ ρ t hΛ hρ.le b B hb P Q k‖^2) ≤
        constant P Q ρ hρ hρhalf * B^2 * t^(-(1/2 : ℝ)) *
          MatrixNegativeLocalization.energy Λ ρ (difference P Q) := by
  have hh := jets hΛ hρ hρhalf ht ht1 b B hB hb P Q [] (fun _ => 0) (fun _ => le_rfl) (by simp)
  have he (k : d × HaarNode) : jetColumn Λ ρ t hΛ hρ.le b B hb P Q [] k =
      column Λ ρ t hΛ hρ.le b B hb P Q k := by
    dsimp only [jetColumn, MatrixHaarHigherFamily.jet, DirectionalJets.jet]
    rw [MatrixHaarHigherFamily.column_realize, MatrixHaarHigherFamily.column_realize]
    rfl
  simpa only [he, List.length_nil, MatrixJetClosure.weight, List.map_nil, List.prod_nil, one_pow, mul_one] using hh

end SHEStochastic.MatrixSignedNegativeHeat
