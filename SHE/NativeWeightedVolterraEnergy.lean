module
public import SHE.NativeWeightedVolterra
public import SHE.BieleckiKernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.NativeWeightedVolterraEnergy
open MeasureTheory Set PredictableL2 LowBands Filter Topology
open scoped NNReal ENNReal
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- A weak inverse-weight bound suffices for the stopped Bielecki
contraction. It uses the actual native Volterra path integral. -/
theorem energy(μ:Measure Ω)[SFinite μ](H:ℝ≥0){Λ γ:ℝ}(hΛ:0≤Λ)(hγ:0<γ)
    (U:ℝ≥0→Ω→StateL2)(hU:Measurable (Function.uncurry U))
    (hmem:∀ω,MemLp (fun s:ℝ≥0=>Real.exp (-γ*(s:ℝ)) • U s ω) 2 (timeMeasure H)):
    (∫⁻t,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖NativeClock.volterra Λ (fun s=>U s ω) t‖^2) ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal ((H:ℝ)/(2*(Λ+γ)))*
        (∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂μ ∂timeMeasure H):=by
  let c:ℝ:=1/(2*(Λ+γ))
  have hc:0≤c:=by dsimp [c];positivity
  have hm:Measurable (fun p:ℝ≥0×Ω=>ENNReal.ofReal
      (Real.exp (-2*γ*(p.1:ℝ))*‖U p.1 p.2‖^2)):=
    ENNReal.continuous_ofReal.measurable.comp
      ((((measurable_coe_nnreal_real.comp measurable_fst).const_mul (-2*γ)).exp).mul
        (hU.norm.pow_const 2))
  have hb(t:ℝ≥0)(ht:t≤H)(ω:Ω):
      ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖NativeClock.volterra Λ (fun s=>U s ω) t‖^2)≤
        ENNReal.ofReal c*(∫⁻s,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂timeMeasure H):=by
    have htm:timeMeasure t≤timeMeasure H:=by
      rw [←timeMeasure_restrict ht]
      exact Measure.restrict_le_self
    have hft:MemLp (fun s:ℝ≥0=>Real.exp (-γ*(s:ℝ)) • U s ω) 2 (timeMeasure t):=
      (hmem ω).mono_measure htm
    have hi:Integrable (fun s:ℝ≥0=>Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) (timeMeasure t):=by
      simpa only [NativeWeightedVolterra.norm_weight_sq] using hft.norm.integrable_sq
    have hh:=ENNReal.ofReal_le_ofReal (NativeWeightedVolterra.section_energy hΛ hγ t (fun s=>U s ω) hft)
    rw [ENNReal.ofReal_mul hc,ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (fun s=>mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))] at hh
    exact hh.trans (mul_le_mul_right (lintegral_mono' htm le_rfl) (ENNReal.ofReal c))
  calc
    _≤∫⁻t,∫⁻ω,ENNReal.ofReal c*
        (∫⁻s,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂timeMeasure H) ∂μ ∂timeMeasure H:=by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem H] with t ht
      exact lintegral_mono (hb t ht.2)
    _=(ENNReal.ofReal (H:ℝ)*ENNReal.ofReal c)*
        (∫⁻ω,∫⁻s,ENNReal.ofReal (Real.exp (-2*γ*(s:ℝ))*‖U s ω‖^2) ∂timeMeasure H ∂μ):=by
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const,timeMeasure_mass]
      ring
    _=_:=by
      have he:(H:ℝ)*c=(H:ℝ)/(2*(Λ+γ)):=by dsimp [c];ring
      have hcoef:ENNReal.ofReal (H:ℝ)*ENNReal.ofReal c=ENNReal.ofReal ((H:ℝ)/(2*(Λ+γ))):=
        (ENNReal.ofReal_mul H.2).symm.trans (congrArg ENNReal.ofReal he)
      exact congrArg₂ (fun x y:ℝ≥0∞=>x*y) hcoef (lintegral_lintegral_swap hm.aemeasurable).symm

/-- The deterministic drift and stochastic Bielecki coefficients can
be made simultaneously small after fixing the actual damping. -/
theorem exists_weight(A K:ℝ):∃γ:ℝ,1≤γ ∧
    A/γ+K*BieleckiKernel.mass γ≤1/8:=by
  have h0:Tendsto (fun γ:ℝ=>A/γ) atTop (𝓝 0):=by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul A
  have h1:Tendsto (fun γ:ℝ=>K*BieleckiKernel.mass γ) atTop (𝓝 0):=by
    simpa only [mul_zero] using BieleckiKernel.mass_tends_zero.const_mul K
  have hlim:Tendsto (fun γ:ℝ=>A/γ+K*BieleckiKernel.mass γ) atTop (𝓝 0):=by
    simpa only [add_zero] using h0.add h1
  have he:=(hlim.eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1/8))).and
    (eventually_ge_atTop (1:ℝ))
  obtain ⟨γ,hγ,hγ1⟩:=he.exists
  exact ⟨γ,hγ1,hγ.le⟩
end SHE.NativeWeightedVolterraEnergy
