module
public import SHE.GaussianCircleMass
public import SHE.NativeCircleDistance
public import SHE.NativeGaussianSpatialSchur
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeGaussianCircleMass
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatSpan
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

def G (s L:ℝ)(z:HeatCircle×HeatCircle):ℝ:=GaussianCircleMass.decay s L (dist z.1 z.2)
def mass (s L:ℝ):ℝ:=2*(1+1/(s-1))*(2*Real.pi*L)⁻¹

theorem measurable_G (s L:ℝ):Measurable (G s L):=by
  unfold G GaussianCircleMass.decay
  fun_prop

theorem zero_mass {s L:ℝ}(hs:1<s)(hL:0<L):
    (∫x:HeatCircle,GaussianCircleMass.decay s L ‖x‖ ∂haarAddCircle)≤mass s L:=by
  have he:(fun x:HeatCircle=>GaussianCircleMass.decay s L ‖x‖)=
      fun x=>GaussianCircleMass.decay s (2*Real.pi*L) ‖unitCenter x‖:=by
    funext x
    rw [NativeCircleDistance.norm_scale]
    unfold GaussianCircleMass.decay
    congr 2
    ring
  rw [he]
  have hp:0<2*Real.pi*L:=by positivity
  have hi: (∫x:HeatCircle,GaussianCircleMass.decay s (2*Real.pi*L) ‖unitCenter x‖ ∂haarAddCircle)=
      ∫x:UnitAddCircle,GaussianCircleMass.decay s (2*Real.pi*L) ‖x‖ ∂haarAddCircle:=
    (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).integral_comp
      (CircleNormalization.scaleMeasurableEquiv (2*Real.pi) 1).measurableEmbedding
      (fun x:UnitAddCircle=>GaussianCircleMass.decay s (2*Real.pi*L) ‖x‖)
  rw [hi]
  exact GaussianCircleMass.mass hs hp

theorem row {s L:ℝ}(hs:1<s)(hL:0<L)(x:HeatCircle):
    (∫y:HeatCircle,G s L (x,y) ∂haarAddCircle)≤mass s L:=by
  have he:(∫y:HeatCircle,G s L (x,y) ∂haarAddCircle)=
      ∫y:HeatCircle,GaussianCircleMass.decay s L ‖y‖ ∂haarAddCircle:=by
    simp only [G,dist_comm x,dist_eq_norm]
    exact integral_sub_right_eq_self (μ:=haarAddCircle) (fun y:HeatCircle=>GaussianCircleMass.decay s L ‖y‖) x
  rw [he]
  exact zero_mass hs hL

theorem col {s L:ℝ}(hs:1<s)(hL:0<L)(y:HeatCircle):
    (∫x:HeatCircle,G s L (x,y) ∂haarAddCircle)≤mass s L:=by
  have he:(fun x:HeatCircle=>G s L (x,y))=fun x=>G s L (y,x):=by
    funext x
    exact congrArg (GaussianCircleMass.decay s L) (dist_comm x y)
  rw [he]
  exact row hs hL y

/-- Genuine native-circle polynomial Gaussian cancellation has its
sharp spatial inverse-scale gain inside the positive heat Schur bound. -/
theorem schur {s L t A0:ℝ}(hs:1<s)(hL:0<L)(ht:0<t)(hA0:0≤A0)
    (A:HeatCircle→ℝ)(hA:Measurable A)(hAb:∀x,|A x|≤A0):
    (∫x:HeatCircle,∫y:HeatCircle,NativeHeatQuadratic.K t ht (x,y)*G s L (x,y)*A x*A y
      ∂haarAddCircle ∂haarAddCircle)≤
      min 1 ((1+heatConstant*(t/2)^(-(1/2:ℝ)))*mass s L)*
        (∫x:HeatCircle,A x^2 ∂haarAddCircle):=by
  apply NativeGaussianSpatialSchur.bound ht
    (by unfold mass;positivity) hA0 (G s L) (measurable_G s L)
    (fun z=>GaussianCircleMass.decay_nonneg hL.le dist_nonneg)
    (fun z=>min_le_left _ _) (row hs hL) (col hs hL) A hA hAb

end SHE.NativeGaussianCircleMass
