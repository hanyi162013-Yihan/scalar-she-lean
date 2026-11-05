module
public import SHE.CanonicalGaussianRootBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace SHE.CanonicalGaussianBareRoot
open Set MeasureTheory SmoothCylinders UniformSmooth WordRecursion StoppedFourier
variable (D:SmoothApproximation.ScalarData)
def test(n band:ℕ):HeatCircle→State 1→ℝ:=fun _ z=>ScalarHeatBands.band (D.smoothCoefficient n) band (z 0)
theorem uniform(n band:ℕ):UniformBoundedSmooth (test D n band):=
  UniformBoundedSmooth.fixed ((ScalarHeatBands.band_boundedSmooth (D.smooth_boundedSmooth n) band).comp_right
    (EuclideanSpace.proj (0:Fin 1)))
theorem measurable(n band:ℕ):Measurable (fun z:HeatCircle×State 1=>test D n band z.1 z.2):=
  ((ScalarHeatBands.band_boundedSmooth (D.smooth_boundedSmooth n) band).comp_right
    (EuclideanSpace.proj (0:Fin 1))).smooth.continuous.measurable.comp measurable_snd
theorem test_one(n band:ℕ):CanonicalGaussianRootBands.test D n (fun _:HeatCircle=>(1:ℝ)) band=test D n band:=by
  funext x z
  change 1*ScalarHeatBands.band (D.smoothCoefficient n) band (z 0)=ScalarHeatBands.band (D.smoothCoefficient n) band (z 0)
  exact one_mul _
end SHE.CanonicalGaussianBareRoot
