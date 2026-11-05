module

public import SHE.GaussianCoordinates
public import SHE.MeasurableGaussianScores

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ScoreProjectionEnergy
open Set MeasureTheory GaussianIncrement GaussianCoordinates MeasurableGaussianScores
open scoped InnerProductSpace BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {n m : ℕ}

theorem sum_eq_selected (f : Fin m → Fin n) (hf : Function.Injective f)
    (F : Fin n → ℝ) (hF : ∀ i, i ∉ Set.range f → F i=0) :
    (∑ i : Fin n, F i)=∑ j : Fin m, F (f j) := by
  classical
  have hs : (∑ i ∈ Finset.univ.image f, F i)=∑ i : Fin n, F i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply hF i
    simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using hi
  rw [Finset.sum_image (fun i _ j _ h => hf h)] at hs
  exact hs.symm

theorem inner_commute {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (x y : State n) :
    inner ℝ x (Matrix.toEuclideanCLM (𝕜:=ℝ) A y)=
      inner ℝ y (Matrix.toEuclideanCLM (𝕜:=ℝ) A x) := by
  rw [Matrix.inner_toEuclideanCLM,Matrix.inner_toEuclideanCLM]
  simpa only [star_trivial] using hA.isHermitian.star_dotProduct_mulVec_comm
    (fun i => x i) (fun i => y i)

theorem scoreVariance_eq_solution {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {d : State n} (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (v : State n) (hv : Matrix.toEuclideanCLM (𝕜:=ℝ) A v=d) :
    scoreVariance A d=inner ℝ v d := by
  calc
    _ = inner ℝ (coefficient A d) (Matrix.toEuclideanCLM (𝕜:=ℝ) A v) := by rw [hv]; rfl
    _ = inner ℝ v (Matrix.toEuclideanCLM (𝕜:=ℝ) A (coefficient A d)) := inner_commute hA _ _
    _ = _ := by
      rw [show Matrix.toEuclideanCLM (𝕜:=ℝ) A (coefficient A d)=d from
        (by simpa only [coefficient] using MeasurableGeneralizedInverse.generalizedInverse_on_range A hd)]

theorem projection_operator (f : Fin m → Fin n) (hf : Function.Injective f)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hzero : ∀ i, i ∉ Set.range f → ∀ j, A j i=0) (u : State n) :
    projection f (Matrix.toEuclideanCLM (𝕜:=ℝ) A u)=
      Matrix.toEuclideanCLM (𝕜:=ℝ) (A.submatrix f f) (projection f u) := by
  ext j
  change (∑ i : Fin n, A (f j) i*u i) = ∑ i : Fin m, A (f j) (f i)*u (f i)
  exact sum_eq_selected f hf _ (fun i hi => by rw [hzero i hi (f j),zero_mul])

/-- A singular Gaussian score energy is unchanged by adding zero
covariance coordinates. This permits spatial AE estimates in the actual
earlier frame before later insertion locations are chosen. -/
theorem scoreVariance_projection (f : Fin m → Fin n) (hf : Function.Injective f)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (hzero : ∀ i, i ∉ Set.range f → ∀ j, A j i=0)
    {d : State n} (hd : d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (hdzero : ∀ i, i ∉ Set.range f → d i=0) :
    scoreVariance A d=scoreVariance (A.submatrix f f) (projection f d) := by
  have hresponse : Matrix.toEuclideanCLM (𝕜:=ℝ) A (coefficient A d)=d :=
    by simpa only [coefficient] using MeasurableGeneralizedInverse.generalizedInverse_on_range A hd
  have hsol : Matrix.toEuclideanCLM (𝕜:=ℝ) (A.submatrix f f) (projection f (coefficient A d))=
      projection f d := by
    rw [← projection_operator f hf A hzero,hresponse]
  rw [scoreVariance_eq_solution (hA.submatrix f) ⟨_,hsol⟩ _ hsol]
  change inner ℝ (coefficient A d) d=inner ℝ (projection f (coefficient A d)) (projection f d)
  simp only [PiLp.inner_apply,RCLike.inner_apply,star_trivial,projection_apply]
  exact sum_eq_selected f hf _ (fun i hi => by rw [hdzero i hi,zero_mul])

end SHE.ScoreProjectionEnergy
