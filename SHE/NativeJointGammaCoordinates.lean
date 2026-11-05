module
public import SHE.NativeJointPhysicalGammaAlgebra
public import SHE.NativeJointColumnDirections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeJointGammaCoordinates
open Set MeasureTheory FiniteHaar StoppedFourier OrthogonalItoChannels NativeJointColumnDirections
open scoped NNReal ENNReal
variable {Ω:Type*}[MeasurableSpace Ω](v b:ℝ≥0)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)
variable (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)(d:ℝ≥0×Ω→ℝ)

theorem left_block (c:EllipticField m U)(p:ℝ≥0×Ω)(x:HeatCircle)(k:HaarNode):
    left k (NativePhysicalGammaKernel.block b hκ hm c p x)=
      NativeObservationCovariance.row hκ (AdditiveHaarForcing.constantField κ hκ) b p.1 x k:=rfl

theorem right_block (c:EllipticField m U)(p:ℝ≥0×Ω)(x:HeatCircle)(k:HaarNode):
    right k (NativePhysicalGammaKernel.block b hκ hm c p x)=
      NativeObservationCovariance.row hm c b p.1 x k:=rfl

/-- The complete joint scalar input has one unchanged common additive
column. The convex residual weight does not duplicate this channel. -/
theorem left_active (p:ℝ≥0×Ω)(hp:p∈NativeGammaClock.window v b)(x:HeatCircle)(k:HaarNode):
    left k (NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d (p,x))=
      ((g 0 (p,x)).re-(g 3 (p,x)).re-(g 2 (p,x)).re+(g 5 (p,x)).re)*
        NativeObservationCovariance.row hκ (AdditiveHaarForcing.constantField κ hκ) b p.1 x k:=by
  rw [NativeJointPhysicalGammaInput.raw_active v b hκ hm g c0 c1 r0 r1 d p hp x]
  simp only [map_sub,map_smul,map_add,left_block,smul_eq_mul]
  ring

/-- Literal residual common-Haar coordinate of the SAME original
convex input, with every signed current and frozen contribution. -/
theorem right_active (p:ℝ≥0×Ω)(hp:p∈NativeGammaClock.window v b)(x:HeatCircle)(k:HaarNode):
    right k (NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d (p,x))=
      (g 0 (p,x)).re*NativeObservationCovariance.row hm (c0 p) b p.1 x k-
      (g 3 (p,x)).re*NativeObservationCovariance.row hm (r0 p) b p.1 x k-
      (g 2 (p,x)).re*((1-d p)*NativeObservationCovariance.row hm (c0 p) b p.1 x k+
        d p*NativeObservationCovariance.row hm (c1 p) b p.1 x k)+
      (g 5 (p,x)).re*NativeObservationCovariance.row hm (r1 p) b p.1 x k:=by
  rw [NativeJointPhysicalGammaInput.raw_active v b hκ hm g c0 c1 r0 r1 d p hp x]
  simp only [map_sub,map_smul,map_add,right_block,smul_eq_mul]
  ring

theorem inactive (p:ℝ≥0×Ω)(hp:p∉NativeGammaClock.window v b)(x:HeatCircle):
    NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d (p,x)=0:=
  NativeJointPhysicalGammaInput.raw_inactive v b hκ hm g c0 c1 r0 r1 d p hp x
end SHE.NativeJointGammaCoordinates
