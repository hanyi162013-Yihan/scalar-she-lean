module

public import SHEStochastic.MatrixHaarFrechetBounds
public import SHEStochastic.MatrixFieldQuadratic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixPositiveCoordinates
open Matrix MatrixFrobeniusNorm
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff Topology

variable (d : Type*) [Fintype d] [DecidableEq d]

/-- Perturbation coordinates belong to the real symmetric subspace.
Positivity is not being treated as open in all nonsymmetric matrices. -/
def symmetric : Submodule ℝ (Matrix d d ℝ) where
  carrier := {A | A.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' := fun hA hB => hA.add hB
  smul_mem' := fun c A hA => hA.smul (IsSelfAdjoint.all c)

abbrev Coordinates := symmetric d × symmetric d

def left : Coordinates d →L[ℝ] Matrix d d ℝ :=
  (symmetric d).subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)

def right : Coordinates d →L[ℝ] Matrix d d ℝ :=
  (symmetric d).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)

variable {d}

/-- A perturbation smaller than the ellipticity margin stays positive
definite, in the correct symmetric parameter space. -/
theorem positive (A H : Matrix d d ℝ) (hA : A.PosDef) (hH : H.IsHermitian)
    (m : ℝ) (hLo : m • (1 : Matrix d d ℝ) ≤ A) (hSmall : ‖H‖ < m) : (A+H).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hA.isHermitian.add hH)
  intro v hv
  let u : EuclideanSpace ℝ d := WithLp.toLp 2 v
  have hu : u≠0 := by
    intro he
    exact hv (congrArg WithLp.ofLp he)
  have hn : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hlo := MatrixFieldQuadratic.lower A m hLo u
  have hop : ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) H u‖ ≤ ‖H‖*‖u‖ :=
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) H).le_opNorm u
  have hbound := (norm_inner_le_norm (𝕜 := ℝ) u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) H u)).trans
    (mul_le_mul_of_nonneg_left hop (norm_nonneg u))
  have hneg : -‖H‖*‖u‖^2 ≤ inner ℝ u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) H u) := by
    have hh := neg_abs_le (inner ℝ u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) H u))
    rw [← Real.norm_eq_abs] at hh
    nlinarith only [hh, hbound]
  have hdiff : 0 < (m-‖H‖)*‖u‖^2 := mul_pos (sub_pos.mpr hSmall) hn
  have hsum : inner ℝ u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (A+H) u)=
      inner ℝ u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) A u)+
        inner ℝ u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) H u) := by
    rw [map_add, ContinuousLinearMap.add_apply, inner_add_right]
  have hh : 0 < inner ℝ u (Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ) (A+H) u) := by
    rw [hsum]
    nlinarith only [hlo, hneg, hdiff]
  simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using hh

theorem ball_positive (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (m : ℝ) (hLo : m • (1 : Matrix d d ℝ) ≤ A ∧ m • (1 : Matrix d d ℝ) ≤ B) :
    ∀ y∈Metric.ball (0 : Coordinates d) m,
      (A+left d y).PosDef ∧ (B+right d y).PosDef := by
  intro y hy
  have hn : ‖y‖ < m := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  constructor
  · exact positive A (left d y) hA y.1.property m hLo.1 ((norm_fst_le y).trans_lt hn)
  · exact positive B (right d y) hB y.2.property m hLo.2 ((norm_snd_le y).trans_lt hn)

/-- The previous all-order child bounds now apply on an explicit open
ball of genuine symmetric mass coordinates. No open-positive-domain
hypothesis remains as an external analytic input. -/
theorem children (A B : Matrix d d ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hLo : m • (1 : Matrix d d ℝ) ≤ A ∧ m • (1 : Matrix d d ℝ) ≤ B)
    (hHi : A ≤ U • (1 : Matrix d d ℝ) ∧ B ≤ U • (1 : Matrix d d ℝ))
    (n : ℕ) (hn : 0 < n) (v : Fin n → Coordinates d) :
    size (iteratedFDeriv ℝ n (fun y => MatrixHaarAlgebra.left (A+left d y) (B+right d y)) 0 v) ≤
        MatrixHaarJetBounds.childConstant d m U n*
          (∏ i : Fin n, (size ((v i).1 : Matrix d d ℝ)+size ((v i).2 : Matrix d d ℝ))) ∧
    size (iteratedFDeriv ℝ n (fun y => MatrixHaarAlgebra.right (A+left d y) (B+right d y)) 0 v) ≤
        MatrixHaarJetBounds.childConstant d m U n*
          (∏ i : Fin n, (size ((v i).1 : Matrix d d ℝ)+size ((v i).2 : Matrix d d ℝ))) := by
  have hh := MatrixHaarFrechetBounds.children A B (left d) (right d)
    (Metric.ball 0 m) Metric.isOpen_ball (ball_positive A B hA hB m hLo)
    0 (by simpa only [Metric.mem_ball, dist_self] using hm) m U hm hU
    (by simpa only [map_zero, add_zero] using hLo) (by simpa only [map_zero, add_zero] using hHi) n hn v
  exact hh

end SHEStochastic.MatrixPositiveCoordinates
