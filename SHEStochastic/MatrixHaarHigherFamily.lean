module

public import SHEStochastic.MatrixRootJets
public import SHE.HaarConstantJets
public import SHE.HilbertColumns
public import SHEStochastic.FiniteOptionEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHEStochastic.MatrixHaarHigherFamily
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar MatrixPhysicalColumnSmooth
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A single actual nonlinear profile map for every root/detail column. -/
def column (i : d) : HaarNode → Domain (d := d) → Physical (d := d)
  | none => MatrixRootCalculus.root i
  | some p => fun u => MatrixPhysicalColumnMap.detail (MatrixGlobalHaar.child p false) (MatrixGlobalHaar.child p true)
      (MatrixGlobalHaar.child_measurable p false) (MatrixGlobalHaar.child_measurable p true) i u.val

theorem column_realize (P : Profile d) (i : d) (q : HaarNode) :
    column i q (MatrixProfileSymmetry.realize d P) = factor P (lp.single 2 (i, q) 1) := by
  cases q with
  | none => exact MatrixRootJets.global_root P i
  | some p => exact MatrixPhysicalColumnMap.global_detail P p i

def jet (P : Profile d) (w : List (Domain (d := d))) (k : d × HaarNode) : Physical (d := d) :=
  DirectionalJets.jet w (column k.1 k.2) (MatrixProfileSymmetry.realize d P)

def constant (P : Profile d) (k : ℕ) : ℝ :=
  16 * (Fintype.card d : ℝ) * packetHeatConstant * MatrixOneInputColumn.orderConstant P k ^ 2 *
    (DyadicTransport.smoothingConstant (1/2)) ^ 2 +
  (Fintype.card d : ℝ) * MatrixRootJets.orderConstant P k ^ 2

theorem constant_nonneg (P : Profile d) (k : ℕ) : 0 ≤ constant P k := by
  have hP : 0 ≤ packetHeatConstant := zero_le_one.trans packetHeatConstant_one_le
  unfold constant
  positivity

theorem roots {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    (∑ i : d, ‖VectorHeat.heat t (jet P (v :: w) (i, none))‖ ^ 2) ≤
      (Fintype.card d : ℝ) * MatrixRootJets.orderConstant P w.length ^ 2 *
        t ^ (-(1/2 : ℝ)) * ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2 := by
  have htunit : 1 ≤ t ^ (-(1/2 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2 : ℝ) ≤ 0)
  calc
    _ ≤ ∑ i : d, MatrixRootJets.orderConstant P w.length ^ 2 * ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := pow_le_pow_left₀ (norm_nonneg _) (MatrixRootJets.one_input P i v w B hB hRest) 2
      exact (pow_le_pow_left₀ (norm_nonneg _) (VectorHeat.contraction t _) 2).trans
        (hb.trans_eq (by rw [mul_pow, mul_pow]))
    _ = (Fintype.card d : ℝ) * MatrixRootJets.orderConstant P w.length ^ 2 * ‖v‖ ^ 2 *
        MatrixJetClosure.weight B w ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left htunit (by positivity : 0 ≤
        (Fintype.card d : ℝ) * MatrixRootJets.orderConstant P w.length ^ 2 * ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2)
      nlinarith only [hh]

/-- Full countable energy bound, including all roots and cross-state
components, for the actual higher derivative columns of the infinite
matrix Haar factor. -/
theorem energy {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    Summable (fun k : d × HaarNode => ‖VectorHeat.heat t (jet P (v :: w) k)‖ ^ 2) ∧
      (∑' k : d × HaarNode, ‖VectorHeat.heat t (jet P (v :: w) k)‖ ^ 2) ≤
        constant P w.length * t ^ (-(1/2 : ℝ)) * ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2 := by
  have hd := MatrixHigherHeat.details ht ht1 P v w B hB hRest
  have ho := FiniteOptionEnergy.sum (fun k : d × HaarNode => ‖VectorHeat.heat t (jet P (v :: w) k)‖ ^ 2)
    (fun _ => sq_nonneg _) hd.1
  refine ⟨ho.1, ?_⟩
  rw [ho.2]
  exact (add_le_add hd.2 (roots ht ht1 P v w B hB hRest)).trans_eq (by unfold constant; ring)

/-- A genuine Hilbert--Schmidt column space value, ready for native
Hilbert stochastic integration; square summability is a conclusion. -/
def columns {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    HilbertColumns.Space (d × HaarNode) (Physical (d := d)) :=
  HilbertColumns.ofSummable (fun k => VectorHeat.heat t (jet P (v :: w) k)) (energy ht ht1 P v w B hB hRest).1

theorem columns_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (P : Profile d) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (B : Domain (d := d) → ℝ) (hB : ∀ q, 0 ≤ B q)
    (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ B q) :
    ‖columns ht ht1 P v w B hB hRest‖ ^ 2 ≤
      constant P w.length * t ^ (-(1/2 : ℝ)) * ‖v‖ ^ 2 * MatrixJetClosure.weight B w ^ 2 := by
  rw [HilbertColumns.norm_sq]
  exact (energy ht ht1 P v w B hB hRest).2

end SHEStochastic.MatrixHaarHigherFamily
