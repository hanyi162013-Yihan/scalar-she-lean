module
public import SHE.NativeGaussianCircleMass
public import SHE.BoundedSpatialCovariance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeGaussianCovarianceKernel
open Set MeasureTheory Real AddCircle StoppedFourier NativeHeatQuadratic
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

def Q (s L t η:ℝ)(ht:0<t)(z:HeatCircle×HeatCircle):ℝ:=
  K t ht z*(NativeGaussianCircleMass.G s L z+η)
def sup (t η:ℝ):ℝ:=(1+heatConstant*(t/2)^(-(1/2:ℝ)))*(1+η)
def cost (s L t η:ℝ):ℝ:=
  min 1 ((1+heatConstant*(t/2)^(-(1/2:ℝ)))*NativeGaussianCircleMass.mass s L)+η

theorem nonneg {s L t η:ℝ}(hL:0≤L)(hη:0≤η)(ht:0<t)(z:HeatCircle×HeatCircle):0≤Q s L t η ht z:=
  mul_nonneg (norm_nonneg _) (add_nonneg (GaussianCircleMass.decay_nonneg hL dist_nonneg) hη)

theorem measurable (s L t η:ℝ)(ht:0<t):Measurable (Q s L t η ht):=
  (measurable_K ht).mul ((NativeGaussianCircleMass.measurable_G s L).add_const η)

theorem sup_nonneg {t η:ℝ}(ht:0<t)(hη:0≤η):0≤sup t η:=by
  unfold sup
  exact mul_nonneg (add_nonneg (by norm_num)
    (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (by positivity) _))) (by linarith)

theorem bounded {s L t η:ℝ}(hL:0≤L)(hη:0≤η)(ht:0<t)(z:HeatCircle×HeatCircle):
    Q s L t η ht z≤sup t η:=by
  change K t ht z*(NativeGaussianCircleMass.G s L z+η)≤
    (1+heatConstant*(t/2)^(-(1/2:ℝ)))*(1+η)
  have hg:NativeGaussianCircleMass.G s L z≤1:=min_le_left _ _
  have hg0:0≤NativeGaussianCircleMass.G s L z:=GaussianCircleMass.decay_nonneg hL dist_nonneg
  exact mul_le_mul (K_bound ht z) (by linarith) (by linarith)
    (add_nonneg (by norm_num) (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (by positivity) _)))

theorem row {s L t η:ℝ}(hs:1<s)(hL:0<L)(hη:0≤η)(ht:0<t)(x:HeatCircle):
    (∫y:HeatCircle,Q s L t η ht (x,y) ∂haarAddCircle)≤cost s L t η:=by
  let C:ℝ:=1+heatConstant*(t/2)^(-(1/2:ℝ))
  have hC:0≤C:=by
    dsimp [C]
    exact add_nonneg (by norm_num)
      (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (by positivity) _))
  have hiK:Integrable (fun y:HeatCircle=>K t ht (x,y)) haarAddCircle:=by
    apply BoundedSpatialCovariance.integrable haarAddCircle _
      ((measurable_K ht).comp (measurable_const.prodMk measurable_id)) C
    intro y
    change ‖K t ht (x,y)‖≤C
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤K t ht (x,y) from norm_nonneg _)]
    exact K_bound ht (x,y)
  have hiG:Integrable (fun y:HeatCircle=>K t ht (x,y)*NativeGaussianCircleMass.G s L (x,y)) haarAddCircle:=by
    apply (integrable_const C).mono'
      ((((measurable_K ht).mul (NativeGaussianCircleMass.measurable_G s L)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    filter_upwards with y
    change ‖K t ht (x,y)*NativeGaussianCircleMass.G s L (x,y)‖≤C
    have hg0:0≤NativeGaussianCircleMass.G s L (x,y):=GaussianCircleMass.decay_nonneg hL.le dist_nonneg
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (show 0≤K t ht (x,y) from norm_nonneg _) hg0)]
    exact (mul_le_of_le_one_right (norm_nonneg _) (min_le_left _ _)).trans (K_bound ht (x,y))
  have he:(fun y:HeatCircle=>Q s L t η ht (x,y))=
      fun y=>K t ht (x,y)*NativeGaussianCircleMass.G s L (x,y)+K t ht (x,y)*η:=by
    funext y
    dsimp [Q]
    ring
  rw [he,integral_add hiG (hiK.mul_const η),integral_mul_const,K_row ht x,one_mul]
  have hr:=PositiveKernelMarginal.clipped haarAddCircle _ _
    ((measurable_K ht).comp (measurable_const.prodMk measurable_id))
    ((NativeGaussianCircleMass.measurable_G s L).comp (measurable_const.prodMk measurable_id))
    hC (fun y=>norm_nonneg _) (fun y=>K_bound ht (x,y)) (K_row ht x)
    (fun y=>GaussianCircleMass.decay_nonneg hL.le dist_nonneg) (fun y=>min_le_left _ _)
    (NativeGaussianCircleMass.row hs hL x)
  change (∫y:HeatCircle,K t ht (x,y)*NativeGaussianCircleMass.G s L (x,y) ∂haarAddCircle)≤
    min 1 (C*NativeGaussianCircleMass.mass s L) at hr
  change (∫y:HeatCircle,K t ht (x,y)*NativeGaussianCircleMass.G s L (x,y) ∂haarAddCircle)+η≤
    min 1 (C*NativeGaussianCircleMass.mass s L)+η
  linarith

theorem col {s L t η:ℝ}(hs:1<s)(hL:0<L)(hη:0≤η)(ht:0<t)(y:HeatCircle):
    (∫x:HeatCircle,Q s L t η ht (x,y) ∂haarAddCircle)≤cost s L t η:=by
  have he:(fun x:HeatCircle=>Q s L t η ht (x,y))=fun x=>Q s L t η ht (y,x):=by
    funext x
    dsimp [Q,K,NativeGaussianCircleMass.G]
    rw [NativeHeatSpan.kernel_symm ht x y,dist_comm x y]
  rw [he]
  exact row hs hL hη ht y

end SHE.NativeGaussianCovarianceKernel
