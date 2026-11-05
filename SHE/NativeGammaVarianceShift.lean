module
public import SHE.ControlledScalarCovarianceTail
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeGammaVarianceShift
open ControlledScalarCovarianceTail StoppedFourier
/-- Exact absolute-to-relative canonical scalar covariance. This is the
variance of the original frozen reference, retaining its past clock. -/
theorem tail_relative (P:CanonicalCovariance.ProfileParameters) (Λ v q b θ:ℝ)
    (hqb:q≤b) (u d:CircleL2) (x:HeatCircle):
    tail P Λ v q b θ u d x=tail P Λ 0 (q-v) (b-v) θ u d x := by
  unfold tail
  rw [ScalarCovarianceTailScale.diagonal_eq _ hqb,
    ScalarCovarianceTailScale.diagonal_eq _ (sub_le_sub_right hqb v)]
  rw [show (b-v)-(q-v)=b-q by ring]
  congr 1
  funext p
  change ControlledProfile.profile P Λ u d (θ,(p.1+q-v,p.2))=
    ControlledProfile.profile P Λ u d (θ,(p.1+(q-v)-0,p.2))
  congr 2
  ring
end SHE.NativeGammaVarianceShift
