module
public import SHE.NativeVolterraSectionEnergy
public import SHE.TimeMeasureRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeWeightedVolterra
open MeasureTheory Set PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

theorem integral_eq(d:ℝ)(f:ℝ≥0→StateL2)(t:ℝ≥0):
    NativeClock.volterra d f t=∫s,Real.exp (-d*((t:ℝ)-(s:ℝ))) •
      NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (f s) ∂timeMeasure t:=by
  rw [timeMeasure_integral]
  have hi:=intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ))
    (f:=fun s:ℝ=>Real.exp (-d*((t:ℝ)-s)) • NativeHeatObservation.heat ((t:ℝ)-s) (f s.toNNReal)) t.2
  change (∫s in (0:ℝ)..(t:ℝ),Real.exp (-d*((t:ℝ)-s)) •
    NativeHeatObservation.heat ((t:ℝ)-s) (f s.toNNReal))=_
  exact hi.trans (by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [Real.coe_toNNReal _ hs.1.le])

theorem conjugate(Λ γ:ℝ)(f:ℝ≥0→StateL2)(t:ℝ≥0):
    Real.exp (-γ*(t:ℝ)) • NativeClock.volterra Λ f t=
      NativeClock.volterra (Λ+γ) (fun s:ℝ≥0=>Real.exp (-γ*(s:ℝ)) • f s) t:=by
  rw [integral_eq,integral_eq,←integral_smul]
  apply integral_congr_ae
  filter_upwards with s
  rw [map_smul,smul_smul,smul_smul,←Real.exp_add,←Real.exp_add]
  congr 1
  congr 1
  ring

theorem norm_weight_sq(γ:ℝ)(t:ℝ≥0)(v:StateL2):
    ‖Real.exp (-γ*(t:ℝ)) • v‖^2=Real.exp (-2*γ*(t:ℝ))*‖v‖^2:=by
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow]
  congr 1
  rw [pow_two,←Real.exp_add]
  congr 1
  ring

/-- The native weighted Volterra section has a genuine inverse-weight
energy gain; no sharp operator norm is needed for stopped uniqueness. -/
theorem section_energy {Λ γ:ℝ}(hΛ:0≤Λ)(hγ:0<γ)(t:ℝ≥0)(f:ℝ≥0→StateL2)
    (hf:MemLp (fun s:ℝ≥0=>Real.exp (-γ*(s:ℝ)) • f s) 2 (timeMeasure t)):
    Real.exp (-2*γ*(t:ℝ))*‖NativeClock.volterra Λ f t‖^2≤
      (1/(2*(Λ+γ)))*(∫s,Real.exp (-2*γ*(s:ℝ))*‖f s‖^2 ∂timeMeasure t):=by
  rw [←norm_weight_sq,conjugate,integral_eq]
  have hh:=NativeVolterraSectionEnergy.section_energy (by linarith:0<Λ+γ) t
    (fun s:ℝ≥0=>Real.exp (-γ*(s:ℝ)) • f s) hf
  simpa only [norm_weight_sq] using hh
end SHE.NativeWeightedVolterra
