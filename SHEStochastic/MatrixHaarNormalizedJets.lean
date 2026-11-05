module

public import SHEStochastic.MatrixHaarJetBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixFrobeniusNorm
open Matrix SHE.FiniteTransport

open scoped Matrix.Norms.Frobenius in
theorem smul {d k : Type*} [Fintype d] [Fintype k] (c : ℝ) (A : Matrix d k ℝ) :
    size (c • A) = |c| * size A := by
  have he (B : Matrix d k ℝ) : size B=‖B‖ := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    unfold size
    congr 1
    simp only [frobeniusSq, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simpa only [he, Real.norm_eq_abs] using norm_smul c A

end SHEStochastic.MatrixFrobeniusNorm

namespace SHEStochastic.MatrixHaarNormalizedJets
open Matrix DirectionalJets MatrixFrobeniusNorm MatrixJetClosure MatrixHaarJetBounds
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For two child masses with the same length `c`, every actual mixed
Haar coefficient has the explicit length factor `c^(-1/2)`. The other
constant depends only on normalized ellipticity, dimension and order. -/
theorem children (a b : Matrix d d ℝ) (L R : E →L[ℝ] Matrix d d ℝ)
    (s : Set E) (hs : IsOpen s)
    (hp : ∀ y∈s, (a+L y).PosDef ∧ (b+R y).PosDef)
    (x : E) (hx : x∈s) (m U : ℝ) (hm : 0 < m) (hU : 0 < U)
    (hLo : m • (1 : Matrix d d ℝ) ≤ a+L x ∧ m • (1 : Matrix d d ℝ) ≤ b+R x)
    (hHi : a+L x ≤ U • (1 : Matrix d d ℝ) ∧ b+R x ≤ U • (1 : Matrix d d ℝ))
    (c : ℝ) (hc : 0 < c) (w : List E) (hw : w≠[]) :
    size (jet w (fun y => MatrixHaarAlgebra.left (c • (a+L y)) (c • (b+R y))) x) ≤
        (Real.sqrt c)⁻¹*(childConstant d m U w.length*weight (fun v => size (L v)+size (R v)) w) ∧
    size (jet w (fun y => MatrixHaarAlgebra.right (c • (a+L y)) (c • (b+R y))) x) ≤
        (Real.sqrt c)⁻¹*(childConstant d m U w.length*weight (fun v => size (L v)+size (R v)) w) := by
  have hA : ∀ y∈s, ContDiffAt ℝ ∞ (fun z => a+L z) y :=
    fun _ _ => contDiffAt_const.add L.contDiff.contDiffAt
  have hB : ∀ y∈s, ContDiffAt ℝ ∞ (fun z => b+R z) y :=
    fun _ _ => contDiffAt_const.add R.contDiff.contDiffAt
  have he := MatrixHaarScaling.children_jets _ _ s hs hA hB hp x hx c hc w
  have hb := MatrixHaarJetBounds.children a b L R s hs hp x hx m U hm hU hLo hHi w hw
  have hn : 0 ≤ (Real.sqrt c)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg c)
  constructor
  · rw [he.1, MatrixFrobeniusNorm.smul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left hb.1 hn
  · rw [he.2, MatrixFrobeniusNorm.smul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left hb.2 hn

end SHEStochastic.MatrixHaarNormalizedJets
