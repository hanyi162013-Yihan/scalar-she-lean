module
public import SHE.NativeJointPhysicalGammaInput
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SHE.NativeJointPhysicalGammaInput
open Set MeasureTheory FiniteHaar StoppedFourier OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω:Type*} [MeasurableSpace Ω] (v b:ℝ≥0)
variable {κ m U:ℝ} (hκ:0<κ) (hm:0<m)
variable (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U) (d:ℝ≥0×Ω→ℝ)

/-- The literal joint scalar row has the convex combination of the
two actual Haar rows. No factor of an averaged coefficient is used. -/
theorem raw_active (p:ℝ≥0×Ω) (hp:p∈NativeGammaClock.window v b) (x:HeatCircle):
    raw v b hκ hm g c0 c1 r0 r1 d (p,x)=
      ((g 0 (p,x)).re • NativePhysicalGammaKernel.block b hκ hm (c0 p) p x-
        (g 3 (p,x)).re • NativePhysicalGammaKernel.block b hκ hm (r0 p) p x)-
      ((g 2 (p,x)).re • ((1-d p) • NativePhysicalGammaKernel.block b hκ hm (c0 p) p x+
        d p • NativePhysicalGammaKernel.block b hκ hm (c1 p) p x)-
        (g 5 (p,x)).re • NativePhysicalGammaKernel.block b hκ hm (r1 p) p x):=by
  classical
  simp only [raw,NativePhysicalGammaKernel.raw,if_pos hp]
  module

theorem raw_inactive (p:ℝ≥0×Ω) (hp:p∉NativeGammaClock.window v b) (x:HeatCircle):
    raw v b hκ hm g c0 c1 r0 r1 d (p,x)=0:=by
  classical
  simp only [raw,NativePhysicalGammaKernel.raw,if_neg hp,smul_zero,add_zero]

end SHE.NativeJointPhysicalGammaInput
