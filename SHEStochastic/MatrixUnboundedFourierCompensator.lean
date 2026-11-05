module

public import SHEStochastic.MatrixUnboundedStateCovariance
public import SHEStochastic.ContinuousCanonicalCompensator
public import SHEStochastic.MatrixFourierSquareTests
public import SHEStochastic.MatrixFourierMixedTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixUnboundedFourierCompensator
open MeasureTheory SHE MatrixInfiniteHaar Matrix MatrixFourierCoordinates
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1) (H : ℝ≥0)
    (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ)

/-- The actual unbounded quadratic Fourier compensator. -/
def square (t : ℝ≥0) : CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
    (ι := Fin n×SHE.FiniteHaar.HaarNode) H → ℝ :=
  ContinuousCanonicalCompensator.value H (2*(freq : ℝ)^2) (by positivity)
    (MatrixUnboundedStateCovariance.covariance G hG hβ hβ1 i i (weight a freq) (weight a freq)) t

/-- The mixed bracket retains the same original Haar driver coordinate. -/
def mixed (k : Fin n×SHE.FiniteHaar.HaarNode) (t : ℝ≥0) :
    CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H → ℝ :=
  ContinuousCanonicalCompensator.value H ((freq : ℝ)^2) (sq_nonneg _)
    (MatrixUnboundedStateCovariance.mixed G hG hβ hβ1 i (weight a freq)
      (VectorWhiteCoordinates.analysis.symm (MatrixPredictableHaarRotation.basis k))) t

theorem square_adapted : StronglyAdapted (SHE.CanonicalStateDriverFiltration.filtration H)
    (square G hG hβ hβ1 H i a freq) := ContinuousCanonicalCompensator.adapted _ _ _ _

theorem mixed_adapted (k : Fin n×SHE.FiniteHaar.HaarNode) :
    StronglyAdapted (SHE.CanonicalStateDriverFiltration.filtration H)
      (mixed G hG hβ hβ1 H i a freq k) := ContinuousCanonicalCompensator.adapted _ _ _ _

variable (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ)
    {K : Set (SHE.CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H)} (hK : IsCompact K)

include hK in
/-- The actual cutoff quadratic compensators converge uniformly on
compact joint state/noise path sets to the literal unbounded one. -/
theorem cutoff_square (t : ℝ≥0) :
    TendstoUniformlyOn (fun m : ℕ => MatrixFourierSquareTests.compensator H
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i a freq t)
      (square G hG hβ hβ1 H i a freq t) Filter.atTop K := by
  let bn : ℕ → C(Physical (d := Fin n),ℝ) := fun m =>
    (MatrixFourierCompensator.diagonal (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i a freq).toContinuousMap
  have hb (s : Set (Physical (d := Fin n))) (hs : IsCompact s) :
      TendstoUniformlyOn (fun m => bn m)
        (MatrixUnboundedStateCovariance.covariance G hG hβ hβ1 i i (weight a freq) (weight a freq)) Filter.atTop s :=
    MatrixUnboundedStateCovariance.cutoff_covariance G hG hβ hβ1 ell hell hLower hs i i (weight a freq) (weight a freq)
  change TendstoUniformlyOn (fun m => ContinuousCanonicalCompensator.value H (2*(freq : ℝ)^2)
    (by positivity) (bn m) t) _ Filter.atTop K
  exact ContinuousCanonicalCompensator.uniformly_on_compact H (2*(freq : ℝ)^2) (by positivity) bn _ hb hK t

include hK in
/-- The same convergence retains the actual original-noise mixed
compensator, not merely a matching covariance in another realization. -/
theorem cutoff_mixed (k : Fin n×SHE.FiniteHaar.HaarNode) (t : ℝ≥0) :
    TendstoUniformlyOn (fun m : ℕ => MatrixFourierMixedTests.compensator H
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i a freq k t)
      (mixed G hG hβ hβ1 H i a freq k t) Filter.atTop K := by
  let bn : ℕ → C(Physical (d := Fin n),ℝ) := fun m =>
    (MatrixFourierCompensator.mixed (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i a freq
      (MatrixPredictableHaarRotation.basis k)).toContinuousMap
  have hb (s : Set (Physical (d := Fin n))) (hs : IsCompact s) :
      TendstoUniformlyOn (fun m => bn m)
        (MatrixUnboundedStateCovariance.mixed G hG hβ hβ1 i (weight a freq)
          (VectorWhiteCoordinates.analysis.symm (MatrixPredictableHaarRotation.basis k))) Filter.atTop s :=
    MatrixUnboundedStateCovariance.cutoff_mixed G hG hβ hβ1 ell hell hLower hs i (weight a freq)
      (VectorWhiteCoordinates.analysis.symm (MatrixPredictableHaarRotation.basis k))
  change TendstoUniformlyOn (fun m => ContinuousCanonicalCompensator.value H ((freq : ℝ)^2)
    (sq_nonneg _) (bn m) t) _ Filter.atTop K
  exact ContinuousCanonicalCompensator.uniformly_on_compact H ((freq : ℝ)^2) (sq_nonneg _) bn _ hb hK t

end SHEStochastic.MatrixUnboundedFourierCompensator
