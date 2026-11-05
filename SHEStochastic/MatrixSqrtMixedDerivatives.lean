module

public import SHEStochastic.DirectionalJetPartitions
public import SHEStochastic.MatrixSqrtDerivative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixSqrtMixedDerivatives
open Matrix Filter SHE.FiniteTransport DirectionalJets
open scoped MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Proper mixed terms in the derivative of the actual square identity.
Every factor has positive order strictly less than the whole word. -/
def remainder (A : E → Matrix d d ℝ) (w : List E) (x : E) : Matrix d d ℝ :=
  ((properPairs w).map (fun p ↦ jet p.1 (fun y ↦ CFC.sqrt (A y)) x *
    jet p.2 (fun y ↦ CFC.sqrt (A y)) x)).sum

variable (A : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
  (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hpos : ∀ y∈s, (A y).PosDef)
  (x : E) (hx : x∈s)

include hs hA hpos hx in
/-- Actual full mixed Leibniz identity, for arbitrary directions and
arbitrary order, on an open positive-definite parameter domain. -/
theorem leibniz (w : List E) :
    ((pairs w).map (fun p ↦ jet p.1 (fun y ↦ CFC.sqrt (A y)) x *
      jet p.2 (fun y ↦ CFC.sqrt (A y)) x)).sum = jet w A x := by
  have hS : ∀ y∈s, ContDiffAt ℝ ∞ (fun z ↦ CFC.sqrt (A z)) y := by
    intro y hy
    apply MatrixSqrtSmooth.comp (hA y hy) (hpos y hy)
    filter_upwards [hs.mem_nhds hy] with z hz
    exact (hpos z hz).posSemidef.nonneg
  have he : (fun y ↦ CFC.sqrt (A y)*CFC.sqrt (A y)) =ᶠ[𝓝 x] A := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact CFC.sqrt_mul_sqrt_self (A y) (hpos y hy).posSemidef.nonneg
  exact (DirectionalJets.mul s hs x hx w _ _ hS hS).symm.trans (DirectionalJets.congr w he)

include hs hA hpos hx in
/-- The full mixed derivative solves a Sylvester equation whose source
contains only the covariance derivative and strictly lower square-root
jets. This does not assume that covariance matrices commute. -/
theorem sylvester (w : List E) (hw : w≠[]) :
    CFC.sqrt (A x)*jet w (fun y ↦ CFC.sqrt (A y)) x +
      jet w (fun y ↦ CFC.sqrt (A y)) x*CFC.sqrt (A x) =
        jet w A x-remainder A w x := by
  have hh := sum_pairs_split w hw (fun p ↦ jet p.1 (fun y ↦ CFC.sqrt (A y)) x *
    jet p.2 (fun y ↦ CFC.sqrt (A y)) x)
  simp only [jet] at hh
  exact eq_sub_of_add_eq (hh.symm.trans (leibniz A s hs hA hpos x hx w))

include hs hA hpos hx in
/-- Uniform elliptic coercivity for EVERY actual mixed square-root jet.
The coefficient is independent of matrix dimension and dyadic depth. -/
theorem bound (w : List E) (hw : w≠[]) (r : ℝ) (hr : 0≤r)
    (hLo : r^2 • (1 : Matrix d d ℝ) ≤ A x) :
    (2*r)^2*frobeniusSq (jet w (fun y ↦ CFC.sqrt (A y)) x) ≤
      frobeniusSq (jet w A x-remainder A w x) := by
  have hsym : (CFC.sqrt (A x))ᵀ = CFC.sqrt (A x) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (A x)).posSemidef.isHermitian.eq
  have hh := MatrixSylvesterFrobenius.lower (CFC.sqrt (A x)) (CFC.sqrt (A x))
    (jet w (fun y ↦ CFC.sqrt (A y)) x) r r (by linarith)
    (MatrixSqrtDerivative.quadratic_lower (A x) r hr hLo)
    (by rw [hsym]; exact MatrixSqrtDerivative.quadratic_lower (A x) r hr hLo)
  rw [sylvester A s hs hA hpos x hx w hw] at hh
  convert hh using 1 <;> ring

end SHEStochastic.MatrixSqrtMixedDerivatives
