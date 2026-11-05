module

public import SHE.FiniteGaussianAveraging
public import SHE.GaussianNegativePacket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! The actual positive squared physical circle heat kernel as a finite
heat-tree measure, with its exact spatial mass and dependent averaging. -/
namespace SHE.HeatTreeAveraging
open Set MeasureTheory AddCircle Real CircleHeat HeatMarkov HeatTorusKernel
  GaussianNegativePacket FiniteGaussianAveraging StoppedFourier FiniteHaar
local instance : Fact (0<(1:ℝ)):=⟨by positivity⟩

abbrev Circle:=AddCircle (1:ℝ)

def heatSquareMeasure (t:ℝ)(ht:0<t):Measure Circle:=
  haarAddCircle.withDensity (fun y=>ENNReal.ofReal (‖kernel t ht y‖^2))

theorem heatSquareWeight_integrable (t:ℝ)(ht:0<t):
    Integrable (fun y:Circle=>‖kernel t ht y‖^2) haarAddCircle:=by
  exact (kernel t ht).continuous.norm.pow 2 |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

instance heatSquareMeasure_finite (t:ℝ)(ht:0<t):IsFiniteMeasure (heatSquareMeasure t ht):=
  isFiniteMeasure_withDensity_ofReal (heatSquareWeight_integrable t ht).hasFiniteIntegral

theorem integral_heatSquareMeasure (t:ℝ)(ht:0<t)(F:Circle→ℝ):
    (∫y,F y ∂heatSquareMeasure t ht)=∫y,‖kernel t ht y‖^2*F y ∂haarAddCircle:=by
  rw[heatSquareMeasure,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  simp only[ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

theorem heatSquareMeasure_mass (t:ℝ)(ht:0<t):
    (heatSquareMeasure t ht).real univ=‖unitHeatKernel t (0:Circle)‖^2:=by
  have hconst:(∫_:Circle,(1:ℝ) ∂heatSquareMeasure t ht)=(heatSquareMeasure t ht).real univ:=by simp
  rw[←hconst,integral_heatSquareMeasure]
  simp only[mul_one]
  rw[L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards[unitHeatKernel_ae ht (0:Circle)] with y hy
  simp only[sub_zero] at hy
  rw[hy]

theorem heatSquareMeasure_mass_bound {t:ℝ}(ht:0<t)(ht1:t≤1):
    (heatSquareMeasure t ht).real univ≤traceConstant*t^(-(1/2:ℝ)):=by
  rw[heatSquareMeasure_mass,kernel_norm_sq ht]
  have hh:=heatWeight_trace_bound ht
  have hone:1≤t^(-(1/2:ℝ)):=by
    simpa using rpow_le_rpow_of_nonpos ht ht1 (by norm_num:-(1/2:ℝ)≤0)
  have hG:0≤HeatTrace.fractionalGaussianIntegral 0:=(HeatTrace.fractionalGaussianIntegral_pos (by norm_num:(0:ℝ)<1/2)).le
  exact hh.trans (by unfold traceConstant;nlinarith)

/-- Genuine squared heat-kernel averaging, retaining the relative spatial
coordinate inside the actual word. The cost is the exact heat-square mass. -/
theorem heat_square_average (t:ℝ)(ht:0<t)(F:Circle×Circle→ℝ)(hF:Measurable F)
    (hF2:Integrable (fun p=>F p^2) ((heatSquareMeasure t ht).prod haarAddCircle)):
    Integrable (fun x=>(∫y,‖kernel t ht y‖^2*F (y,x) ∂haarAddCircle)^2) haarAddCircle ∧
      (∫x,(∫y,‖kernel t ht y‖^2*F (y,x) ∂haarAddCircle)^2 ∂haarAddCircle)≤
        ‖unitHeatKernel t (0:Circle)‖^2*(∫p,F p^2 ∂(heatSquareMeasure t ht).prod haarAddCircle):=by
  have hh:=square_average_le (heatSquareMeasure t ht) haarAddCircle F hF hF2
  simp_rw[integral_heatSquareMeasure] at hh
  rw[heatSquareMeasure_mass] at hh
  exact hh

end SHE.HeatTreeAveraging
