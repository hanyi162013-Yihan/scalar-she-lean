module

public import SHEStochastic.MatrixFieldOperator
public import SHEStochastic.MatrixHaarPairings

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixHaarLpColumns
open MeasureTheory Matrix MatrixHaarFunctions MatrixHaarAlgebra
open scoped NNReal Matrix.Norms.L2Operator

variable {X d : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  [Fintype d] [DecidableEq d] (κ : X → Matrix d d ℝ)

def coefficientField (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    BoundedFieldOperator.Field μ (EuclideanSpace ℝ d) (EuclideanSpace ℝ d) :=
  MatrixFieldOperator.field (column μ κ s t) (measurable_column μ κ s t hs ht)
    (‖left (mass μ κ s) (mass μ κ t)‖₊+‖right (mass μ κ s) (mass μ κ t)‖₊) (by
      filter_upwards with x
      exact (norm_add_le _ _).trans (add_le_add
        (norm_indicator_le_norm_self (s := s) (fun _ : X => left (mass μ κ s) (mass μ κ t)) x)
        (norm_indicator_le_norm_self (s := t) (fun _ : X => right (mass μ κ s) (mass μ κ t)) x)))


def raw (s t : Set X) (i : d) (x : X) : EuclideanSpace ℝ d :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (column μ κ s t x) (EuclideanSpace.single i 1)

theorem memLp (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) (i : d) :
    MemLp (raw μ κ s t i) 2 μ := by
  let F := coefficientField μ κ s t hs ht
  apply MemLp.of_bound (F.measurable.apply_continuousLinearMap (EuclideanSpace.single i 1))
    ((F.bound : ℝ)*‖EuclideanSpace.single i (1 : ℝ)‖)
  filter_upwards [F.norm_bound] with x hx
  exact (F.value x).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def vector (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) (i : d) :
    Lp (EuclideanSpace ℝ d) 2 μ := (memLp μ κ s t hs ht i).toLp _

theorem vector_ae (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) (i : d) :
    ⇑(vector μ κ s t hs ht i) =ᵐ[μ] raw μ κ s t i :=
  (memLp μ κ s t hs ht i).coeFn_toLp

theorem components_ae (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) (i : d) :
    ∀ᵐ x ∂μ, ∀ p, vector μ κ s t hs ht i x p = column μ κ s t x p i := by
  filter_upwards [vector_ae μ κ s t hs ht i] with x hx
  intro p
  rw [hx]
  simp [raw, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Literal spatial pairing for any two matrix Haar columns. -/
theorem pairing (hκ : Measurable κ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖≤ B) (s t u v : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) (hv : MeasurableSet v)
    (i j : d) :
    inner ℝ (vector μ κ s t hs ht i)
      (MatrixFieldOperator.operator κ hκ B hBound (vector μ κ u v hu hv j)) =
      ∫ x, ∑ p : d, ∑ q : d,
        column μ κ s t x p i*κ x p q*column μ κ u v x q j ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [components_ae μ κ s t hs ht i, components_ae μ κ u v hu hv j,
    MatrixFieldOperator.operator_ae κ hκ B hBound (vector μ κ u v hu hv j)] with x hi hj hm
  have hmul (p : d) := congrFun hm p
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hi]
  simp only [Matrix.mulVec, dotProduct, hj] at hmul
  apply Finset.sum_congr rfl
  intro p hp
  rw [hmul p]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The actual vector-valued spatial `L²` columns have all Kronecker
weighted pairings, including off-diagonal state components. -/
theorem weighted_gram (hκ : Measurable κ) (hInt : Integrable κ μ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖≤ B) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef) (i j : d) :
    inner ℝ (vector μ κ s t hs ht i)
      (MatrixFieldOperator.operator κ hκ B hBound (vector μ κ s t hs ht j)) =
        if i=j then 1 else 0 := by
  rw [pairing μ κ hκ B hBound s t s t hs ht hs ht i j]
  exact MatrixHaarPairings.components μ κ hInt s t hs ht hd hA hB i j

/-- Spatially disjoint matrix Haar blocks are orthogonal in the actual
weighted vector `L²` pairing. -/
theorem disjoint (hκ : Measurable κ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖≤ B) (s t u v : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hd : Disjoint (s∪t) (u∪v)) (i j : d) :
    inner ℝ (vector μ κ s t hs ht i)
      (MatrixFieldOperator.operator κ hκ B hBound (vector μ κ u v hu hv j)) = 0 := by
  rw [pairing μ κ hκ B hBound s t u v hs ht hu hv i j]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x∈s∪t
  · have hn : x∉u∪v := fun h => Set.disjoint_left.mp hd hx h
    simp [MatrixHaarFunctions.support μ κ u v x hn]
  · simp [MatrixHaarFunctions.support μ κ s t x hx]


theorem cross_entry (P K Q : Matrix d d ℝ) (i j : d) :
    (Pᴴ*K*Q) i j = ∑ p : d, ∑ q : d, P p i*K p q*Q q j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem pairing_matrix (hκ : Measurable κ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖≤ B) (s t u v : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hInt : Integrable (fun x => (column μ κ s t x)ᴴ*κ x*column μ κ u v x) μ) (i j : d) :
    inner ℝ (vector μ κ s t hs ht i)
      (MatrixFieldOperator.operator κ hκ B hBound (vector μ κ u v hu hv j)) =
      (∫ x, (column μ κ s t x)ᴴ*κ x*column μ κ u v x ∂μ) i j := by
  rw [pairing μ κ hκ B hBound s t u v hs ht hu hv i j]
  have hh := (MatrixHaarPairings.entry i j).integral_comp_comm hInt
  change (∫ x, ((column μ κ s t x)ᴴ*κ x*column μ κ u v x) i j ∂μ) = _ at hh
  apply Eq.trans _ hh
  apply integral_congr_ae
  filter_upwards with x
  exact (cross_entry _ _ _ i j).symm

/-- The actual vector columns of a finer block are orthogonal to a
coarser block that is constant on its two children. -/
theorem nested (hκ : Measurable κ) (hInt : Integrable κ μ) (B : ℝ≥0)
    (hBound : ∀ᵐ x ∂μ, ‖κ x‖≤ B) (s t u v : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hA : (mass μ κ u).PosDef) (hB : (mass μ κ v).PosDef)
    (C : Matrix d d ℝ) (hC : ∀ x∈u∪v, column μ κ s t x=C) (i j : d) :
    inner ℝ (vector μ κ s t hs ht i)
      (MatrixFieldOperator.operator κ hκ B hBound (vector μ κ u v hu hv j)) = 0 := by
  have he : (fun x => (column μ κ s t x)ᴴ*κ x*column μ κ u v x) =
      (fun x => Cᴴ*(κ x*column μ κ u v x)) := by
    funext x
    by_cases hx : x∈u∪v
    · rw [hC x hx, Matrix.mul_assoc]
    · simp [MatrixHaarFunctions.support μ κ u v x hx]
  have hCross : Integrable (fun x => (column μ κ s t x)ᴴ*κ x*column μ κ u v x) μ := by
    rw [he]
    exact (MatrixHaarFunctions.integrable_weighted μ κ hInt u v hu hv).const_mul Cᴴ
  rw [pairing_matrix μ κ hκ B hBound s t u v hs ht hu hv hCross i j,
    MatrixHaarPairings.nested μ κ hInt u v hu hv hA hB _ C hC]
  rfl

end SHEStochastic.MatrixHaarLpColumns
