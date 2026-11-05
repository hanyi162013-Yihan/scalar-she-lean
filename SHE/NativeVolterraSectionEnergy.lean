module
public import SHE.NativeControlMass
public import SHE.NativeClock
public import SHE.IntegralEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeVolterraSectionEnergy
open MeasureTheory Set PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

theorem norm_integral_smul_sq {X E:Type*}[MeasurableSpace X]
    [NormedAddCommGroup E][NormedSpace ℝ E](μ:Measure X)
    (a:X→ℝ)(v:X→E)(ha:MemLp a 2 μ)(hv:MemLp v 2 μ):
    ‖∫x,a x • v x ∂μ‖^2≤(∫x,‖a x‖^2 ∂μ)*(∫x,‖v x‖^2 ∂μ):=by
  have hp:(2:ℝ).HolderConjugate 2:=by rw [Real.holderConjugate_iff];norm_num
  have ha':MemLp a (ENNReal.ofReal (2:ℝ)) μ:=by simpa using ha
  have hv':MemLp (fun x=>‖v x‖) (ENNReal.ofReal (2:ℝ)) μ:=by simpa using hv.norm
  have hs:=integral_mul_norm_le_Lp_mul_Lq hp ha' hv'
  simp only [norm_norm,Real.rpow_two] at hs
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hs
  have hn:‖∫x,a x • v x ∂μ‖≤(∫x,‖a x‖*‖v x‖ ∂μ):=by
    simpa only [norm_smul] using norm_integral_le_integral_norm (fun x=>a x • v x)
  have hh:=pow_le_pow_left₀ (norm_nonneg _) (hn.trans hs) 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _=>sq_nonneg _)),
    Real.sq_sqrt (integral_nonneg (fun _=>sq_nonneg _))] at hh
  exact hh

/-- Cauchy--Schwarz retains an inverse damping factor in one actual
native heat convolution section. It applies to any genuine L2 input. -/
theorem section_energy {d:ℝ}(hd:0<d)(t:ℝ≥0)(f:ℝ≥0→StateL2)
    (hf:MemLp f 2 (timeMeasure t)):
    ‖∫s,Real.exp (-d*((t:ℝ)-(s:ℝ))) •
      NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (f s) ∂timeMeasure t‖^2≤
      (1/(2*d))*(∫s,‖f s‖^2 ∂timeMeasure t):=by
  let a:ℝ≥0→ℝ:=fun s=>Real.exp (-d*((t:ℝ)-(s:ℝ)))
  let v:ℝ≥0→StateL2:=fun s=>NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (f s)
  have ha:MemLp a 2 (timeMeasure t):=by
    apply MemLp.of_bound (show Continuous a by dsimp [a];fun_prop).aestronglyMeasurable 1
    filter_upwards [timeMeasure_ae_mem t] with s hs
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have hs':(s:ℝ)≤(t:ℝ):=by exact_mod_cast hs.2
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le)
      (sub_nonneg.mpr hs'))
  have hvmeas:AEStronglyMeasurable v (timeMeasure t):=by
    have ht:Measurable (fun s:ℝ≥0=>((t:ℝ)-(s:ℝ))/NativeHeatObservation.timeScale):=by fun_prop
    have hh:=RealHeat.continuous_realHeat_action.comp_aestronglyMeasurable
      (ht.aestronglyMeasurable.prodMk hf.aestronglyMeasurable)
    change AEStronglyMeasurable v (timeMeasure t) at hh
    exact hh
  have hvnorm(s:ℝ≥0):‖v s‖≤‖f s‖:=RealHeat.realHeat_contraction _ _
  have hv:MemLp v 2 (timeMeasure t):=hf.of_le hvmeas (ae_of_all _ hvnorm)
  have he:(fun s:ℝ≥0=>‖a s‖^2)=(fun s:ℝ≥0=>Real.exp (-(2*d)*((t:ℝ)-(s:ℝ)))):=by
    funext s
    dsimp only [a]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,pow_two,←Real.exp_add]
    congr 1
    ring
  have hmass:(∫s,‖a s‖^2 ∂timeMeasure t)≤1/(2*d):=by
    rw [he]
    apply (le_div_iff₀ (by positivity:0<2*d)).mpr
    have hh:=NativeControlMass.exponential_mass (2*d) t
    nlinarith only [hh,(Real.exp_pos (-(2*d)*(t:ℝ))).le]
  have hve:(∫s,‖v s‖^2 ∂timeMeasure t)≤∫s,‖f s‖^2 ∂timeMeasure t:=
    integral_mono_ae hv.norm.integrable_sq hf.norm.integrable_sq
      (ae_of_all _ (fun s=>pow_le_pow_left₀ (norm_nonneg _) (hvnorm s) 2))
  exact (norm_integral_smul_sq (timeMeasure t) a v ha hv).trans
    (mul_le_mul hmass hve (integral_nonneg (fun _=>sq_nonneg _)) (by positivity))
end SHE.NativeVolterraSectionEnergy
