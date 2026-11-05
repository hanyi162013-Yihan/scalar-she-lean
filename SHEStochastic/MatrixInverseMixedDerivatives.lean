module

public import SHEStochastic.DirectionalJetPartitions
public import SHEStochastic.MatrixHaarSmooth

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixInverseMixedDerivatives
open Matrix Filter DirectionalJets
open scoped MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered lower-order products in the inverse identity. -/
def remainder (A : E → Matrix d d ℝ) (w : List E) (x : E) : Matrix d d ℝ :=
  ((properPairs w).map (fun p ↦ jet p.1 A x * jet p.2 (fun y ↦ (A y)⁻¹) x)).sum

/-- Every actual mixed inverse jet is expressed through strictly lower
inverse jets and the given covariance jets. No auxiliary derivative
family or commutation condition is supplied. -/
theorem formula (A : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hUnit : ∀ y∈s, IsUnit (A y))
    (x : E) (hx : x∈s) (w : List E) (hw : w≠[]) :
    jet w (fun y ↦ (A y)⁻¹) x =
      -((A x)⁻¹ * (jet w A x*(A x)⁻¹ + remainder A w x)) := by
  have hInv : ∀ y∈s, ContDiffAt ℝ ∞ (fun z ↦ (A z)⁻¹) y :=
    fun y hy ↦ MatrixHaarSmooth.inverse (hA y hy) (hUnit y hy)
  have he : (fun y ↦ A y*(A y)⁻¹) =ᶠ[𝓝 x] (fun _ ↦ (1 : Matrix d d ℝ)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hUnit y hy))
  have hp := DirectionalJets.mul s hs x hx w A (fun y ↦ (A y)⁻¹) hA hInv
  have hzero : ((pairs w).map (fun p ↦ jet p.1 A x*jet p.2 (fun y ↦ (A y)⁻¹) x)).sum=0 :=
    hp.symm.trans ((DirectionalJets.congr w he).trans (jet_const w hw 1 x))
  have hh := sum_pairs_split w hw (fun p ↦ jet p.1 A x*jet p.2 (fun y ↦ (A y)⁻¹) x)
  simp only [jet] at hh
  have hsum : A x*jet w (fun y ↦ (A y)⁻¹) x +
      (jet w A x*(A x)⁻¹+remainder A w x)=0 := by
    exact (add_assoc _ _ _).symm.trans (hh.symm.trans hzero)
  have hiso := eq_neg_of_add_eq_zero_left hsum
  calc
    _ = (A x)⁻¹*(A x*jet w (fun y ↦ (A y)⁻¹) x) :=
      (Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).mp (hUnit x hx))).symm
    _ = _ := by rw [hiso, mul_neg]

end SHEStochastic.MatrixInverseMixedDerivatives
