module
public import SHE.NativeJointColumnDirections
public import SHE.NativeFourierNoiseRows
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeFourierRowAverage
open MeasureTheory AddCircle StoppedFourier FiniteHaar OrthogonalItoChannels
  NativeFourierNoiseRows NativeJointColumnDirections
open scoped NNReal ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

variable {C:Type*}[NormedAddCommGroup C][NormedSpace ℝ C][CompleteSpace C]

/-- A real linear complex coordinate of the spatial Fourier integral
is the corresponding actual Bochner average of the original noise row. -/
theorem projection (R:HeatCircle→C)(hR:Integrable R haarAddCircle)
    (L:C→L[ℝ]ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(w:ℝ):
    a ((w:ℂ)*∫x:HeatCircle,fourier (-l) x*(L (R x):ℂ) ∂haarAddCircle)=
      L (∫x:HeatCircle,(w*a (fourier (-l) x)) • R x ∂haarAddCircle):=by
  have hiC:Integrable (fun x:HeatCircle=>fourier (-l) x*(L (R x):ℂ)) haarAddCircle:=
    ((Complex.ofRealCLM.comp L).integrable_comp hR).bdd_mul
      (fourier (-l)).continuous.measurable.aestronglyMeasurable
      (ae_of_all _ (fun x=>show ‖fourier (-l) x‖≤(1:ℝ) by simp [fourier_apply]))
  have hbound:∀x:HeatCircle,‖w*a (fourier (-l) x)‖≤‖w‖*‖a‖:=by
    intro x
    calc
      _=‖w‖*‖a (fourier (-l) x)‖:=norm_mul _ _
      _≤‖w‖*(‖a‖*‖fourier (-l) x‖):=mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg _)
      _=‖w‖*‖a‖:=by simp [fourier_apply]
  have hiW:Integrable (fun x:HeatCircle=>(w*a (fourier (-l) x)) • R x) haarAddCircle:=
    hR.bdd_smul (𝕜:=ℝ) (φ:=fun x:HeatCircle=>w*a (fourier (-l) x)) (‖w‖*‖a‖)
      (measurable_const.mul (a.continuous.measurable.comp (fourier (-l)).continuous.measurable)).stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ hbound)
  rw [←L.integral_comp_comm hiW]
  change a (w • (∫x:HeatCircle,fourier (-l) x*(L (R x):ℂ) ∂haarAddCircle))=_
  rw [map_smul,←a.integral_comp_comm hiC,←integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_smul]
  change w*a (fourier (-l) x*(L (R x):ℂ))=(w*a (fourier (-l) x))*L (R x)
  rw [mul_comm (fourier (-l) x),show (L (R x):ℂ)*fourier (-l) x=L (R x) • fourier (-l) x from rfl,map_smul]
  change w*(L (R x)*a (fourier (-l) x))=(w*a (fourier (-l) x))*L (R x)
  ring

/-- Both original noise channels are recovered, coordinate by coordinate,
from the actual complete Hilbert Fourier columns. -/
theorem row (R:HeatCircle→Both RealHaarInput)(hR:Integrable R haarAddCircle)
    (K0 K1:Columns)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(w:ℝ)
    (h0:∀k:HaarNode,coefficient l (K0 k)=(w:ℂ)*∫x:HeatCircle,fourier (-l) x*(left k (R x):ℂ) ∂haarAddCircle)
    (h1:∀k:HaarNode,coefficient l (K1 k)=(w:ℂ)*∫x:HeatCircle,fourier (-l) x*(right k (R x):ℂ) ∂haarAddCircle):
    WithLp.toLp 2 (HilbertColumns.mapCLM (a.comp (coefficient l)) K0,
      HilbertColumns.mapCLM (a.comp (coefficient l)) K1)=
      ∫x:HeatCircle,(w*a (fourier (-l) x)) • R x ∂haarAddCircle:=by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply lp.ext
    funext k
    change a (coefficient l (K0 k))=left k (∫x:HeatCircle,(w*a (fourier (-l) x)) • R x ∂haarAddCircle)
    rw [h0 k]
    exact projection R hR (left k) a l w
  · apply lp.ext
    funext k
    change a (coefficient l (K1 k))=right k (∫x:HeatCircle,(w*a (fourier (-l) x)) • R x ∂haarAddCircle)
    rw [h1 k]
    exact projection R hR (right k) a l w
end SHE.NativeFourierRowAverage
