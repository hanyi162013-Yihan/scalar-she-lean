module

public import SHE.UncutScoreChain
public import SHE.OldIntervalGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ProjectedUncutWord
open Set MeasureTheory ProbabilityTheory WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffCarriers GaussianCoordinates TriangularScoreWords
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable {L : CutoffWordLevel.Level R P n}

/-- Only the original newest coordinate must be absent from its own and
earlier interval increments. All remaining coordinates may be correlated. -/
def Chain.CoordinateSupport {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Prop :=
  match chain with
  | .root _ _ => True
  | .step j q f qg prev ht old residual ho hr hc d hd hrg =>
      prev.CoordinateSupport ∧
        ∀ K ∈ ((GaussianTriangularKernel.kernel old residual d,
          leaf L j q (qg 0)) :: prev.word).map Prod.fst,
          ∀ᵐ x ∂K.measure, K.shift x (qg 0) = 0

theorem Chain.triangular_of_coordinateSupport {k : ℕ} {p : History P k}
    {g : Fin (n+k) → Fin N} (chain : Chain L k p g) (hs : chain.CoordinateSupport) :
    Triangular chain.word := by
  induction chain with
  | root p f => trivial
  | step k p f g prev ht old residual ho hr hc d hd hrange ih =>
    obtain ⟨hprev, hz⟩ := hs
    refine ⟨ih hprev, ?_⟩
    intro K hK z
    filter_upwards [hz K hK] with x hx
    change (1 / 2 : ℝ) * (R.totalVariance ((z + K.shift x) (g 0)) -
      R.reference ((carrier L k).nodeTime p,p.2.2)) = _
    have he : (z + K.shift x) (g 0) = z (g 0) := by
      change z (g 0) + K.shift x (g 0) = z (g 0)
      rw [hx, add_zero]
    rw [he]
    rfl

end SHE.ProjectedUncutWord

namespace SHE.GaussianTriangularKernel
open Set MeasureTheory ProbabilityTheory GaussianIncrement
variable {n : ℕ}

/-- Vanishing actual covariance rows imply the original old and residual
Gaussian vectors both have zero increment in this leaf coordinate. -/
theorem coordinate_support_of_zero_rows {R B : MeasurableGeneralizedInverse.Mat n}
    (hR : R.PosSemidef) (hB : B.PosSemidef) (d : State n) (i : Fin n)
    (hRi : ∀ j, R i j = 0) (hBi : ∀ j, B i j = 0) :
    ∀ᵐ x ∂(kernel R B d).measure, (kernel R B d).shift x i = 0 := by
  have h₁ := (Measure.quasiMeasurePreserving_fst
    (μ := multivariateGaussian (0 : State n) R) (ν := multivariateGaussian (0 : State n) B)).ae
    (OldIntervalCovariance.gaussian_coordinate_zero hR i hRi)
  have h₂ := (Measure.quasiMeasurePreserving_snd
    (μ := multivariateGaussian (0 : State n) R) (ν := multivariateGaussian (0 : State n) B)).ae
    (OldIntervalCovariance.gaussian_coordinate_zero hB i hBi)
  filter_upwards [h₁, h₂] with x hx hy
  change x.1 i + x.2 i = 0
  rw [hx, hy, add_zero]

end SHE.GaussianTriangularKernel
