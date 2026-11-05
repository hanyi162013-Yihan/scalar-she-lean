module

public import SHEStochastic.MatrixUnboundedFourierCompensator
public import SHEStochastic.HolderCoefficientEnergyGrowth
public import SHEStochastic.CanonicalEnergyGrowth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedCompensatorGrowth
open MeasureTheory SHE MatrixInfiniteHaar Matrix MatrixFourierCoordinates
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)

def rowConstant (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) : ℝ :=
  ‖k‖^2*(4*(‖MatrixDiffusionRows.row i (G 0)‖+(C : ℝ))^2)

theorem rowConstant_nonneg (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) :
    0≤rowConstant G (C := C) i k := by unfold rowConstant;positivity

theorem diagonal (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := Fin n)) :
    ‖MatrixUnboundedStateCovariance.covariance G hG hβ hβ1 i i k k u‖≤
      rowConstant G (C := C) i k*(1+‖u‖^2) :=
  HolderCoefficientEnergyGrowth.diagonal_bound ν (MatrixDiffusionRows.holder hG i) hβ hβ1 k u

theorem mixed (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) (b : Physical (d := Fin n))
    (u : Physical (d := Fin n)) :
    ‖MatrixUnboundedStateCovariance.mixed G hG hβ hβ1 i k b u‖≤
      (rowConstant G (C := C) i k+‖b‖^2)*(1+‖u‖^2) :=
  HolderCoefficientEnergyGrowth.mixed_bound ν (MatrixDiffusionRows.holder hG i) hβ hβ1 k b u

variable (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
local notation "hG_R" R => MatrixUnboundedCutoff.holder G hG hβ ell hell hLower R

theorem cutoff_diagonal (R : ℝ≥0) (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := Fin n)) :
    ‖MatrixStateNoise.covariance (G_R R) (hG_R R) hβ hβ1 i i k k u‖≤
      rowConstant G (C := C) i k*(1+‖u‖^2) := by
  change ‖StateNoiseCovariance.value ν hβ hβ1
    (UnboundedCoefficientCutoff.holder (MatrixDiffusionRows.holder hG i) R)
    (UnboundedCoefficientCutoff.holder (MatrixDiffusionRows.holder hG i) R) k k u‖≤_
  exact HolderCoefficientEnergyGrowth.cutoff_diagonal_bound ν (MatrixDiffusionRows.holder hG i) hβ hβ1 R k u

theorem cutoff_mixed (R : ℝ≥0) (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) (b : Physical (d := Fin n))
    (u : Physical (d := Fin n)) :
    ‖MatrixStateNoise.cross (G_R R) (hG_R R) hβ hβ1 i k b u‖≤
      (rowConstant G (C := C) i k+‖b‖^2)*(1+‖u‖^2) := by
  change ‖StateDriverCovariance.value ν hβ hβ1
    (UnboundedCoefficientCutoff.holder (MatrixDiffusionRows.holder hG i) R) k b u‖≤_
  exact HolderCoefficientEnergyGrowth.cutoff_mixed_bound ν (MatrixDiffusionRows.holder hG i) hβ hβ1 R k b u

variable (H : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ)

def squareConstant : ℝ :=
  ‖PathIntegratedCovariance.exponential H (2*(freq : ℝ)^2) (by positivity)‖*
    rowConstant G (C := C) i (weight a freq)*(H : ℝ)

theorem squareConstant_nonneg : 0 ≤ squareConstant G (C := C) H i a freq := by
  unfold squareConstant
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (rowConstant_nonneg G i _)) H.property

theorem square_bound (t : ℝ≥0) (x : CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
    (ι := Fin n×SHE.FiniteHaar.HaarNode) H) :
    ‖MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq t x‖≤
      squareConstant G (C := C) H i a freq*(1+‖x.1‖^2) :=
  CanonicalEnergyGrowth.compensator H _ _ _ (rowConstant G (C := C) i (weight a freq))
    (rowConstant_nonneg G i _) (diagonal G hG hβ hβ1 i (weight a freq)) t x

theorem cutoff_square_bound (R : ℝ≥0) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H) :
    ‖MatrixFourierSquareTests.compensator H (G_R R) (hG_R R) hβ hβ1 i a freq t x‖≤
      squareConstant G (C := C) H i a freq*(1+‖x.1‖^2) := by
  change ‖ContinuousCanonicalCompensator.value H (2*(freq : ℝ)^2) (by positivity)
    (MatrixFourierCompensator.diagonal (G_R R) (hG_R R) hβ hβ1 i a freq).toContinuousMap t x‖≤_
  exact CanonicalEnergyGrowth.compensator H _ _ _ (rowConstant G (C := C) i (weight a freq))
    (rowConstant_nonneg G i _) (cutoff_diagonal G hG hβ hβ1 ell hell hLower R i (weight a freq)) t x

def mixedConstant (k : Fin n×SHE.FiniteHaar.HaarNode) : ℝ :=
  ‖PathIntegratedCovariance.exponential H ((freq : ℝ)^2) (sq_nonneg _)‖*
    (rowConstant G (C := C) i (weight a freq)+
      ‖VectorWhiteCoordinates.analysis.symm (MatrixPredictableHaarRotation.basis k)‖^2)*(H : ℝ)

theorem mixedConstant_nonneg (k : Fin n×SHE.FiniteHaar.HaarNode) :
    0 ≤ mixedConstant G (C := C) H i a freq k := by
  unfold mixedConstant
  exact mul_nonneg (mul_nonneg (norm_nonneg _)
    (add_nonneg (rowConstant_nonneg G i _) (sq_nonneg _))) H.property

theorem mixed_bound (k : Fin n×SHE.FiniteHaar.HaarNode) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H) :
    ‖MatrixUnboundedFourierCompensator.mixed G hG hβ hβ1 H i a freq k t x‖≤
      mixedConstant G (C := C) H i a freq k*(1+‖x.1‖^2) :=
  CanonicalEnergyGrowth.compensator H _ _ _ _
    (add_nonneg (rowConstant_nonneg G i _) (sq_nonneg _))
    (mixed G hG hβ hβ1 i (weight a freq)
      (VectorWhiteCoordinates.analysis.symm (MatrixPredictableHaarRotation.basis k))) t x

theorem cutoff_mixed_bound (R : ℝ≥0) (k : Fin n×SHE.FiniteHaar.HaarNode) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
      (ι := Fin n×SHE.FiniteHaar.HaarNode) H) :
    ‖MatrixFourierMixedTests.compensator H (G_R R) (hG_R R) hβ hβ1 i a freq k t x‖≤
      mixedConstant G (C := C) H i a freq k*(1+‖x.1‖^2) := by
  change ‖ContinuousCanonicalCompensator.value H ((freq : ℝ)^2) (sq_nonneg _)
    (MatrixFourierCompensator.mixed (G_R R) (hG_R R) hβ hβ1 i a freq
      (MatrixPredictableHaarRotation.basis k)).toContinuousMap t x‖≤_
  exact CanonicalEnergyGrowth.compensator H _ _ _ _
    (add_nonneg (rowConstant_nonneg G i _) (sq_nonneg _))
    (cutoff_mixed G hG hβ hβ1 ell hell hLower R i (weight a freq)
      (VectorWhiteCoordinates.analysis.symm (MatrixPredictableHaarRotation.basis k))) t x

end SHEStochastic.MatrixUnboundedCompensatorGrowth
