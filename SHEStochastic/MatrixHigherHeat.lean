module

public import SHEStochastic.MatrixOneInputColumn
public import SHEStochastic.MatrixDirectionEnergy
public import SHEStochastic.MatrixPhysicalJetStructure
public import SHEStochastic.VectorHeatPackets
public import SHEStochastic.MatrixPacketFamily
public import SHE.HaarHigherHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixHigherHeat
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixPhysicalColumnSmooth
open MatrixActualColumnCalculus MatrixPhysicalJetStructure MatrixOneInputColumn MatrixDirectionBounds
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem packet {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (p : List Bool) (i : d) (w : List (Domain (d := d))) :
    ‖VectorHeat.heat t (jetColumn P p i w)‖ ^ 2 ≤
      packetHeatConstant * min 1 (nodeLength p ^ 2 / t) * ‖jetColumn P p i w‖ ^ 2 :=
  VectorHeatPackets.packet_min ht ht1 p _ (supported P p i w) (mean_zero P p i w)

theorem column_square (P : Profile d) (p : List Bool) (i : d) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ‖jetColumn P p i (v :: w)‖ ^ 2 ≤
      4 * (childLength p)⁻¹ * orderConstant P w.length ^ 2 *
        MatrixJetClosure.weight B w ^ 2 * localSize p v ^ 2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _)
    (local_L2 P p i v w B hB hRest) 2
  change ‖jetColumn P p i (v :: w)‖ ^ 2 ≤ _ at hh
  have hs : (Real.sqrt (childLength p))⁻¹ ^ 2 = (childLength p)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (childLength_pos p).le]
  apply hh.trans_eq
  simp only [mul_pow, hs]
  ring

theorem component_generation (P : Profile d) (n : ℕ) (i : d) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    (∑ x : Grid n, ‖jetColumn P (leafPath n x) i (v :: w)‖ ^ 2) ≤
      8 * orderConstant P w.length ^ 2 * (((2 ^ (n+1) : ℕ) : ℝ)) *
        ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2 := by
  have hh := MatrixPacketFamily.generation (fun p i => jetColumn P p i (v :: w)) v
    (2 * orderConstant P w.length * MatrixJetClosure.weight B w)
    (fun p i => (local_L2 P p i v w B hB hRest).trans_eq (by ring)) n i
  exact hh.trans_eq (by ring)

theorem heat_generation {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (n : ℕ) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    (∑ x : Grid n, ∑ i : d, ‖VectorHeat.heat t (jetColumn P (leafPath n x) i (v :: w))‖ ^ 2) ≤
      (8 * (Fintype.card d : ℝ) * packetHeatConstant * orderConstant P w.length ^ 2 *
        ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2) *
      (((2 ^ (n+1) : ℕ) : ℝ)) * min 1 ((2 / (((2 ^ (n+1) : ℕ) : ℝ))) ^ 2 / t) := by
  have hh := MatrixPacketFamily.heat_generation (fun p i => jetColumn P p i (v :: w)) v
    (2 * orderConstant P w.length * MatrixJetClosure.weight B w)
    (fun p i => (local_L2 P p i v w B hB hRest).trans_eq (by ring))
    (fun p i => supported P p i (v :: w)) (fun p i => mean_zero P p i (v :: w)) ht ht1 n
  exact hh.trans_eq (by ring)

/-- The actual countable matrix Haar detail family has the integrable
heat Hilbert--Schmidt singularity at every derivative order, with one
arbitrary Frobenius `L²` direction and bounded remaining directions. -/
theorem details {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d))
    (w : List (Domain (d := d))) (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    Summable (fun p : List Bool => ∑ i : d, ‖VectorHeat.heat t (jetColumn P p i (v :: w))‖ ^ 2) ∧
      (∑' p : List Bool, ∑ i : d, ‖VectorHeat.heat t (jetColumn P p i (v :: w))‖ ^ 2) ≤
        (16 * (Fintype.card d : ℝ) * packetHeatConstant * orderConstant P w.length ^ 2 *
          (DyadicTransport.smoothingConstant (1/2)) ^ 2) * t ^ (-(1/2 : ℝ)) *
          ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2 := by
  have hh := MatrixPacketFamily.energy (fun p i => jetColumn P p i (v :: w)) v
    (2 * orderConstant P w.length * MatrixJetClosure.weight B w)
    (fun p i => (local_L2 P p i v w B hB hRest).trans_eq (by ring))
    (fun p i => supported P p i (v :: w)) (fun p i => mean_zero P p i (v :: w)) ht ht1
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

end SHEStochastic.MatrixHigherHeat
