module

public import SHEStochastic.MatrixRootNegative
public import SHEStochastic.MatrixNegativeTrace
public import SHEStochastic.MatrixHaarHigherFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHEStochastic.MatrixHaarNegativeFamily
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.CircleHeat SHE.HaarWeightedHeat
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixProfileEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) : ℝ :=
  MatrixNegativeTrace.constant P ρ hρ hρhalf k +
    (Fintype.card d : ℝ)^2 * (2 * MatrixRootNegative.orderConstant P k^2 * MatrixRootNegativeSlots.count d)

theorem constant_pos (P : Profile d) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (k : ℕ) :
    0 < constant P ρ hρ hρhalf k := by
  have hd := MatrixNegativeTrace.constant_pos P ρ hρ hρhalf k
  have hD : 0 ≤ MatrixRootNegativeSlots.count d := zero_le_one.trans MatrixRootNegativeSlots.count_one
  unfold constant
  positivity

def scalarColumn (P : Profile d) (w : List (Domain (d := d))) (k : d × HaarNode) (r : d) : CircleL2 :=
  realEmbed (component r (MatrixHaarHigherFamily.jet P w k))

def packetEnergy (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P : Profile d) (w : List (Domain (d := d))) (k : d × HaarNode) : ℝ :=
  ∑ r : d, ‖weightedHeat Λ ρ t hΛ hρ b B hb (scalarColumn P w k r)‖ ^ 2

/-- Full negative-input rough-output trace for actual derivatives of
all infinite matrix Haar columns, including every root, detail and
state component. This is a proved analytic input to vector comparison. -/
theorem energy {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d))) (M : Domain (d := d) → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q)
    (b : CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) :
    Summable (packetEnergy Λ ρ t hΛ hρ.le b B hb P (v :: w)) ∧
      (∑' k, packetEnergy Λ ρ t hΛ hρ.le b B hb P (v :: w) k) ≤
        constant P ρ hρ hρhalf w.length * B ^ 2 * t ^ (-(1/2 : ℝ)) *
          MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight M w ^ 2 := by
  have hd := MatrixNegativeTrace.bound hΛ hρ hρhalf ht ht1 P v w M hM hRest b B hB hb
  have he : (fun p => ∑ i : d, packetEnergy Λ ρ t hΛ hρ.le b B hb P (v :: w) (i, some p)) =
      MatrixNegativeGenerations.packetEnergy Λ ρ t hΛ hρ.le b B hb P v w := rfl
  have ho := FiniteOptionEnergy.sum (packetEnergy Λ ρ t hΛ hρ.le b B hb P (v :: w))
    (fun k => Finset.sum_nonneg (fun r _ => sq_nonneg _)) (he ▸ hd.1)
  refine ⟨ho.1, ?_⟩
  rw [ho.2, he]
  have hr : (∑ i : d, packetEnergy Λ ρ t hΛ hρ.le b B hb P (v :: w) (i, none)) ≤
      ((Fintype.card d : ℝ)^2 * (2 * MatrixRootNegative.orderConstant P w.length^2 * MatrixRootNegativeSlots.count d)) *
        B^2 * t^(-(1/2 : ℝ)) * MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight M w^2 := by
    calc
      _ ≤ ∑ i : d, ∑ r : d, (2 * MatrixRootNegative.orderConstant P w.length^2 * MatrixRootNegativeSlots.count d) *
          B^2 * t^(-(1/2 : ℝ)) * MatrixNegativeLocalization.energy Λ ρ v * MatrixJetClosure.weight M w^2 := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun r _ =>
          MatrixRootNegative.pointwise hΛ hρ hρhalf ht ht1 b B hB hb P i r v w M hM hRest))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  exact (add_le_add hd.2 hr).trans_eq (by dsimp only [constant]; ring)

end SHEStochastic.MatrixHaarNegativeFamily
