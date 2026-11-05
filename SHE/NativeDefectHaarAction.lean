module

public import SHE.CommonHaarDefectTrace
public import SHE.NativeClippedHaarDirection

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.NativeDefectHaarAction
open MeasureTheory Real FiniteHaar StoppedFourier StoppedGaussianScore
  GaussianIncrement GaussianTaylorAverage CommonHaarDefectTrace NativeClippedHaarDirection
local instance nativeDefectHaarAction_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeDefectHaarAction_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- Exact original common-Haar realization of the physical joint defect.
The two cross terms and the full quadratic term are all present, and the
stopping and heat-target lists are independent throughout. -/
theorem action_trace {n:ℕ}{m M:ℝ}(hm:0<m)(c d:EllipticField m M)
    (σ target:Fin n→ℝ)(a:Fin n→AddCircle (1:ℝ))(q Λ:ℝ)
    (B:State n→L[ℝ]State n→L[ℝ]ℝ):
    let D:=fun j:HaarNode=>column hm c d σ target a q Λ j
    let V:=fun j:HaarNode=>direction (fun i=>NativeObservationCovariance.row hm d
      (target i) q (nativeCenter a i)) j
    Summable (fun j:HaarNode=>B (D j) (V j)+B (V j) (D j)+B (D j) (D j)) ∧
      covarianceAction (JointNativeDefect.matrix hm Λ σ target (nativeCenter a) c d q) B=
        (∑'j:HaarNode,(B (D j) (V j)+B (V j) (D j)+B (D j) (D j))):=by
  intro D V
  let U:=fun i=>NativeObservationCovariance.row hm c (target i) q (nativeCenter a i)
  let W:=fun i=>NativeObservationCovariance.row hm d (target i) q (nativeCenter a i)
  let r:=fun i=>1-exp (-Λ*(σ i-q))
  have he(j:HaarNode):direction (fun i=>r i • (U i-W i)) j=D j:=by
    apply PiLp.ext
    intro i
    change (r i • (U i-W i)) j= r i*(U i j-W i j)
    simp only [lp.coeFn_smul,lp.coeFn_sub,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  have hh:=full_trace U W r B
  simp only [he] at hh
  exact hh

end SHE.NativeDefectHaarAction
