module

public import SHEStochastic.CutoffNoiseCovarianceConvergence
public import SHEStochastic.MatrixUnboundedCutoff
public import SHEStochastic.MatrixStateNoise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixUnboundedStateCovariance
open MeasureTheory MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) {C β : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)

/-- The literal unbounded matrix component covariance is a continuous
functional on vector L2 states. It retains every off-diagonal entry. -/
def covariance (i j : Fin n) (k l : C(AddCircle (1 : ℝ),ℝ)) : C(Physical (d := Fin n),ℝ) :=
  ⟨StateNoiseCovariance.value ν hβ hβ1 (MatrixDiffusionRows.holder hG i) (MatrixDiffusionRows.holder hG j) k l,
    StateNoiseCovariance.continuous ν hβ hβ1 (MatrixDiffusionRows.holder hG i) (MatrixDiffusionRows.holder hG j) k l⟩

/-- The mixed covariance uses the same fixed physical white-noise
direction as the original-square cutoff equation. -/
def mixed (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) (b : Physical (d := Fin n)) : C(Physical (d := Fin n),ℝ) :=
  ⟨StateDriverCovariance.value ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k b,
    StateDriverCovariance.continuous ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k b⟩

variable (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ)≤G z*(G z)ᴴ)
    {s : Set (Physical (d := Fin n))} (hs : IsCompact s)

include hs in
/-- The actual bounded-cutoff matrix covariances used in the constructed
solutions converge to the literal unbounded state covariance on every
compact L2 state set. No pointwise bound on states is assumed. -/
theorem cutoff_covariance (i j : Fin n) (k l : C(AddCircle (1 : ℝ),ℝ)) :
    TendstoUniformlyOn (fun m : ℕ => MatrixStateNoise.covariance
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i j k l)
      (covariance G hG hβ hβ1 i j k l) Filter.atTop s := by
  change TendstoUniformlyOn (fun m : ℕ => StateNoiseCovariance.value ν hβ hβ1
    (UnboundedCoefficientCutoff.holder (MatrixDiffusionRows.holder hG i) (m : ℝ≥0))
    (UnboundedCoefficientCutoff.holder (MatrixDiffusionRows.holder hG j) (m : ℝ≥0)) k l)
    (StateNoiseCovariance.value ν hβ hβ1 (MatrixDiffusionRows.holder hG i)
      (MatrixDiffusionRows.holder hG j) k l) Filter.atTop s
  exact CutoffNoiseCovarianceConvergence.covariance ν (MatrixDiffusionRows.holder hG i)
    (MatrixDiffusionRows.holder hG j) hβ hβ1 hs k l

include hs in
/-- The original cutoff state/driver bracket converges to the correct
unbounded mixed bracket, on the same compact L2 state sets. -/
theorem cutoff_mixed (i : Fin n) (k : C(AddCircle (1 : ℝ),ℝ)) (b : Physical (d := Fin n)) :
    TendstoUniformlyOn (fun m : ℕ => MatrixStateNoise.cross
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i k b)
      (mixed G hG hβ hβ1 i k b) Filter.atTop s := by
  change TendstoUniformlyOn (fun m : ℕ => StateDriverCovariance.value ν hβ hβ1
    (UnboundedCoefficientCutoff.holder (MatrixDiffusionRows.holder hG i) (m : ℝ≥0)) k b)
    (StateDriverCovariance.value ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k b) Filter.atTop s
  exact CutoffNoiseCovarianceConvergence.mixed ν (MatrixDiffusionRows.holder hG i) hβ hβ1 hs k b

end SHEStochastic.MatrixUnboundedStateCovariance
