module

public import SHEStochastic.ProductIndependence
public import SHEStochastic.FiniteCoordinateIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ProductBrownianFiniteLaw
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal ENNReal
variable {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [DecidableEq ι] [Inhabited ι]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›} {H : ℝ≥0}

def paired (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι) :
    Sum ι ι → ℝ≥0 → IndependentNoiseCompletion.Space μ ν → ℝ :=
  Sum.elim (fun i t z ↦ P.W i t z.1) (fun i t z ↦ Q.W i t z.2)

def leftIndex {n : ℕ} (a : Fin n → Sum ι ι) (i : Fin n) : ι := (a i).elim id (fun _ ↦ default)
def rightIndex {n : ℕ} (a : Fin n → Sum ι ι) (i : Fin n) : ι := (a i).elim (fun _ ↦ default) id
def leftTime {n : ℕ} (a : Fin n → Sum ι ι) (t : Fin n → ℝ≥0) (i : Fin n) : ℝ≥0 :=
  (a i).elim (fun _ ↦ t i) (fun _ ↦ 0)
def rightTime {n : ℕ} (a : Fin n → Sum ι ι) (t : Fin n → ℝ≥0) (i : Fin n) : ℝ≥0 :=
  (a i).elim (fun _ ↦ 0) (fun _ ↦ t i)

theorem law_add_completed_product {n : ℕ}
    {X : Ω → WordRecursion.State n} {Y : Ξ → WordRecursion.State n}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hX : HasLaw X (multivariateGaussian 0 A) μ) (hY : HasLaw Y (multivariateGaussian 0 B) ν) :
    HasLaw (fun z : IndependentNoiseCompletion.Space μ ν ↦ X z.1 + Y z.2)
      (multivariateGaussian 0 (A + B)) (IndependentNoiseCompletion.measure μ ν) := by
  have hi : IndepFun (fun z : IndependentNoiseCompletion.Space μ ν ↦ X z.1)
      (fun z ↦ Y z.2) (IndependentNoiseCompletion.measure μ ν) :=
    indepFun_prod₀ hX.aemeasurable hY.aemeasurable
  have hl := hi.hasLaw_fun_add
    (hX.fun_comp (IndependentNoiseCompletion.fst_preserving μ ν).hasLaw)
    (hY.fun_comp (IndependentNoiseCompletion.snd_preserving μ ν).hasLaw)
  rwa [GaussianIncrement.gaussian_convolution hA hB] at hl

theorem covariance_sum {n : ℕ} (a : Fin n → Sum ι ι) (t : Fin n → ℝ≥0) :
    BrownianFiniteCovariance.matrix (leftIndex a) (leftTime a t) +
      BrownianFiniteCovariance.matrix (rightIndex a) (rightTime a t) =
        BrownianFiniteCovariance.matrix a t := by
  ext i j
  cases hi : a i <;> cases hj : a j <;>
    simp [BrownianFiniteCovariance.matrix, leftIndex, rightIndex, leftTime, rightTime, hi, hj]

/-- Every mixed finite observation of the paired noise has its actual
Gaussian law on the completed original product space. Individual times
and repeated coordinates are retained, including cross-channel covariance. -/
theorem finite_law (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
    (n : ℕ) (a : Fin n → Sum ι ι) (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ H) :
    HasLaw (fun z : IndependentNoiseCompletion.Space μ ν ↦
      WithLp.toLp 2 (fun i ↦ paired P Q (a i) (t i) z))
      (multivariateGaussian 0 (BrownianFiniteCovariance.matrix a t))
      (IndependentNoiseCompletion.measure μ ν) := by
  let X (ω : Ω) : WordRecursion.State n :=
    WithLp.toLp 2 (fun i ↦ P.W (leftIndex a i) (leftTime a t i) ω)
  let Y (ξ : Ξ) : WordRecursion.State n :=
    WithLp.toLp 2 (fun i ↦ Q.W (rightIndex a i) (rightTime a t i) ξ)
  have hL (i) : leftTime a t i ≤ H := by cases hi : a i <;> simp [leftTime, hi, ht i]
  have hR (i) : rightTime a t i ≤ H := by cases hi : a i <;> simp [rightTime, hi, ht i]
  have hl := law_add_completed_product
    (BrownianFiniteCovariance.posSemidef (leftIndex a) (leftTime a t))
    (BrownianFiniteCovariance.posSemidef (rightIndex a) (rightTime a t))
    ((P.law n (leftIndex a)).1 (leftTime a t) hL)
    ((Q.law n (rightIndex a)).1 (rightTime a t) hR)
  rw [covariance_sum] at hl
  apply hl.congr
  filter_upwards [(IndependentNoiseCompletion.fst_preserving μ ν).quasiMeasurePreserving.ae
      (FiniteScalarIto.zero_ae P.toCoordinates default),
    (IndependentNoiseCompletion.snd_preserving μ ν).quasiMeasurePreserving.ae
      (FiniteScalarIto.zero_ae Q.toCoordinates default)] with z hP hQ
  ext i
  cases hi : a i <;>
    simp [paired, X, Y, leftIndex, rightIndex, leftTime, rightTime, hi, hP, hQ]

end SHEStochastic.ProductBrownianFiniteLaw
