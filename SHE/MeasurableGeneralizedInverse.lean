module

public import SHE.RealGramInverse
public import SHE.GaussianGramScore
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! An actual Borel generalized inverse for finite real matrices, valid through
rank changes. It is built by explicit Gram-inverse column branches and a
measurable first-valid-branch choice; no measurable eigenbasis is assumed. -/
namespace SHE.MeasurableGeneralizedInverse
open Set MeasureTheory Matrix Finset RealGramInverse GaussianIncrement
open scoped InnerProductSpace

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

def column (A : Mat n) (i : Fin n) : State n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.basisFun (Fin n) ℝ i)

theorem column_continuous (i : Fin n) : Continuous (fun A : Mat n => column A i) := by
  have hp : Continuous (fun A : Mat n => (A, EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    continuous_id.prodMk continuous_const
  have hh := (Matrix.continuous_uncurry_toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).comp hp
  convert! hh using 1

def branch (I : Finset (Fin n)) (A : Mat n) : State n →ₗ[ℝ] State n where
  toFun d := ∑ i : I, coefficients (fun j : I => column A j) d i •
    EuclideanSpace.basisFun (Fin n) ℝ i
  map_add' d e := by
    simp only [coefficients_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' b d := by
    simp only [coefficients_smul, Pi.smul_apply, smul_smul,
      RingHom.id_apply, smul_eq_mul, Finset.smul_sum]

theorem branch_apply (I : Finset (Fin n)) (A : Mat n) (d : State n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A (branch I A d) =
      projection (fun i : I => column A i) d := by
  simp only [branch, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, projection, column]

/-- Every fixed column branch is jointly Borel in its actual matrix and
physical direction, even when that branch Gram is singular. -/
theorem branch_measurable (I : Finset (Fin n)) :
    Measurable (fun p : Mat n × State n => branch I p.1 p.2) := by
  have hc (i : I) : Measurable (fun p : Mat n × State n =>
      coefficients (fun j : I => column p.1 j) p.2 i) :=
    coefficients_measurable (X := Mat n × State n) (I := I) (G := State n)
      (fun (p : Mat n × State n) (j : I) => column p.1 j)
      (fun p : Mat n × State n => p.2)
      (fun j => ((column_continuous (j : Fin n)).comp
        (continuous_fst : Continuous (fun p : Mat n × State n => p.1))).stronglyMeasurable)
      (continuous_snd : Continuous (fun p : Mat n × State n => p.2)).stronglyMeasurable i
  have he := Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
    (hc i).stronglyMeasurable.smul
      (stronglyMeasurable_const : StronglyMeasurable (fun _ : Mat n × State n =>
        EuclideanSpace.basisFun (Fin n) ℝ (i : Fin n))))
  have hm : StronglyMeasurable (fun p : Mat n × State n => branch I p.1 p.2) := by
    convert! he using 1
    funext p
    simp only [branch, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply']
  exact hm.measurable

def Valid (I : Finset (Fin n)) (A : Mat n) : Prop :=
  ∀ j : Fin n, Matrix.toEuclideanCLM (𝕜 := ℝ) A (branch I A (column A j)) = column A j

theorem operator_apply_measurable :
    Measurable (fun p : Mat n × State n => Matrix.toEuclideanCLM (𝕜 := ℝ) p.1 p.2) := by
  have heq : (fun p : Mat n × State n => Matrix.toEuclideanCLM (𝕜 := ℝ) p.1 p.2) =
      fun p => WithLp.toLp 2 (fun i => ∑ j, p.1 i j * p.2 j) := by
    funext p
    apply (WithLp.equiv 2 (Fin n → ℝ)).injective
    exact Matrix.ofLp_toEuclideanCLM _ _
  rw [heq]
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  apply Finset.measurable_sum
  intro j _
  exact measurable_fst.eval_matrix.mul
    (((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp measurable_snd).eval)

theorem column_measurable (j : Fin n) : Measurable (fun A : Mat n => column A j) :=
  (column_continuous (n := n) j).measurable

theorem branch_column_measurable (I : Finset (Fin n)) (j : Fin n) :
    Measurable (fun A : Mat n => branch I A (column A j)) := by
  have hpair : Measurable (fun A : Mat n => (A, column A j)) :=
    (measurable_id : Measurable (fun A : Mat n => A)).prodMk (column_measurable j)
  convert! (branch_measurable (n := n) I).comp hpair using 1

theorem branch_column_image_measurable (I : Finset (Fin n)) (j : Fin n) :
    Measurable (fun A : Mat n => Matrix.toEuclideanCLM (𝕜 := ℝ) A (branch I A (column A j))) := by
  have hpair : Measurable (fun A : Mat n => (A, branch I A (column A j))) :=
    (measurable_id : Measurable (fun A : Mat n => A)).prodMk (branch_column_measurable I j)
  convert! (operator_apply_measurable (n := n)).comp hpair using 1

theorem valid_entry_measurableSet (I : Finset (Fin n)) (j k : Fin n) :
    MeasurableSet {A : Mat n |
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A (branch I A (column A j))) k = column A j k} := by
  have hl : Measurable (fun A : Mat n =>
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A (branch I A (column A j))) k) :=
    (((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp (branch_column_image_measurable I j)).eval)
  have hr : Measurable (fun A : Mat n => column A j k) :=
    (((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp (column_measurable j)).eval)
  exact measurableSet_eq_fun hl hr

/-- Validity is checked by a finite Borel equality test on genuine matrices. -/
theorem valid_measurableSet (I : Finset (Fin n)) : MeasurableSet {A : Mat n | Valid I A} := by
  have heq : {A : Mat n | Valid I A} = ⋂ j : Fin n, ⋂ k : Fin n,
      {A : Mat n | (Matrix.toEuclideanCLM (𝕜 := ℝ) A (branch I A (column A j))) k = column A j k} := by
    ext A
    simp only [Valid, mem_iInter, mem_ofPred_eq]
    constructor
    · intro h j k
      exact congrArg (fun z : State n => z k) (h j)
    · intro h j
      apply (WithLp.equiv 2 (Fin n → ℝ)).injective
      funext k
      exact h j k
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro k
  exact valid_entry_measurableSet I j k

/-- A finite subset of the actual matrix columns is independent and spans
every column. This is ordinary finite linear algebra, not a rank assumption. -/
theorem exists_independent_columns (A : Mat n) :
    ∃ I : Finset (Fin n), LinearIndependent ℝ (fun i : I => column A i) ∧
      ∀ j, column A j ∈ Submodule.span ℝ (Set.range (fun i : I => column A i)) := by
  obtain ⟨b, _, _, hspan, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty ℝ (column A)) (empty_subset (univ : Set (Fin n)))
  let I : Finset (Fin n) := (Set.toFinite b).toFinset
  have hI : (I : Set (Fin n)) = b := Set.Finite.coe_toFinset (Set.toFinite b)
  have hli' : LinearIndepOn ℝ (column A) (I : Set (Fin n)) := by rwa [hI]
  refine ⟨I, hli'.linearIndependent_restrict, ?_⟩
  intro j
  have hj := hspan (mem_image_of_mem (column A) (mem_univ j))
  have himage : column A '' b = Set.range (fun i : I => column A i) := by
    rw [← hI, Set.image_eq_range]
    rfl
  rwa [himage] at hj

theorem exists_valid (A : Mat n) : ∃ I : Finset (Fin n), Valid I A := by
  obtain ⟨I, hli, hspan⟩ := exists_independent_columns A
  refine ⟨I, ?_⟩
  intro j
  rw [branch_apply]
  exact projection_eq_self (fun i : I => column A i) hli (hspan j)

def subsetAt (n k : ℕ) : Finset (Fin n) :=
  if hk : k < Fintype.card (Finset (Fin n)) then
    (Fintype.equivFin (Finset (Fin n))).symm ⟨k, hk⟩ else ∅

theorem subsetAt_surjective (I : Finset (Fin n)) : ∃ k : ℕ, subsetAt n k = I := by
  let j := Fintype.equivFin (Finset (Fin n)) I
  refine ⟨j.val, ?_⟩
  rw [subsetAt, dite_eq_left j.isLt]
  exact (Fintype.equivFin (Finset (Fin n))).symm_apply_apply I

theorem exists_valid_index (A : Mat n) : ∃ k : ℕ, Valid (subsetAt n k) A := by
  obtain ⟨I, hI⟩ := exists_valid A
  obtain ⟨k, hk⟩ := subsetAt_surjective I
  exact ⟨k, hk ▸ hI⟩

def generalizedInverse (A : Mat n) : State n →ₗ[ℝ] State n := by
  classical
  exact branch (subsetAt n (Nat.find (exists_valid_index A))) A

theorem generalizedInverse_valid (A : Mat n) :
    ∀ j, Matrix.toEuclideanCLM (𝕜 := ℝ) A (generalizedInverse A (column A j)) = column A j := by
  classical
  exact Nat.find_spec (exists_valid_index A)

/-- The selected operator is a genuine right inverse on the actual matrix
range at every rank, including rank zero. -/
theorem generalizedInverse_on_range (A : Mat n) {d : State n}
    (hd : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) A).range) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A (generalizedInverse A d) = d := by
  obtain ⟨z, rfl⟩ := hd
  have hmaps : ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap.comp (generalizedInverse A)).comp
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    exact generalizedInverse_valid A i
  exact congrArg (fun L : State n →ₗ[ℝ] State n => L z) hmaps

/-- Actual joint Borel measurability of the generalized inverse applied to a
physical direction, through arbitrary covariance rank changes. -/
theorem generalizedInverse_measurable :
    Measurable (fun p : Mat n × State n => generalizedInverse p.1 p.2) := by
  classical
  have hf (k : ℕ) : Measurable (fun p : Mat n × State n => branch (subsetAt n k) p.1 p.2) :=
    branch_measurable _
  have hp (k : ℕ) : MeasurableSet {p : Mat n × State n | Valid (subsetAt n k) p.1} :=
    (valid_measurableSet _).preimage measurable_fst
  exact Measurable.find hf hp (fun p : Mat n × State n => exists_valid_index p.1)

end SHE.MeasurableGeneralizedInverse
