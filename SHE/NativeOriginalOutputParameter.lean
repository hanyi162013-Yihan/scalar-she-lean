module
public import SHE.StandardItoParameterFubini
public import SHE.NativeNegativeRealization
public import SHE.NativeOriginalRowsEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeOriginalOutputParameter
open MeasureTheory PredictableL2 StoppedFourier NativeFourierNoiseRows
open scoped ENNReal NNReal
local instance nativeOriginalOutputParameter_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeOriginalOutputParameter_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeOriginalOutputParameter_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeOriginalOutputParameter_lpSigma : MeasurableSpace (HilbertColumns.Space ℤ ℂ):=borel _
local instance nativeOriginalOutputParameter_lpBorel : BorelSpace (HilbertColumns.Space ℤ ℂ):=⟨rfl⟩
variable {Ω:Type*}{X:Type}[MeasurableSpace Ω][MeasurableSpace X]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[SFinite μ]{H:ℝ≥0}

/-- Countable Fourier reconstruction of the same original scalar Ito
outputs. The only version input is ordinary parameterized stochastic
Fubini; the original native output is identified on the specified
parameter measure, without any separability assumption on L²(μ). -/
theorem exists_identified
    (J:StandardTerminalIto (C:=OrthogonalItoChannels.Both Row) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J)(ν:Measure X)[SFinite ν]
    (r i:X→ℤ→Process (E:=OrthogonalItoChannels.Both Row) 𝓕 μ H)
    (R I:ℤ→X×(ℝ≥0×Ω)→OrthogonalItoChannels.Both Row)
    (hR:∀l,StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] (R l))
    (hI:∀l,StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] (I l))
    (hr:∀x l,r x l=ᵐ[energyMeasure μ H] fun p=>R l (x,p))
    (hi:∀x l,i x l=ᵐ[energyMeasure μ H] fun p=>I l (x,p))
    (hRf:∀l,(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖R l (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞)
    (hIf:∀l,(∫⁻x,∫⁻t,∫⁻ω,ENNReal.ofReal (‖I l (x,(t,ω))‖^2) ∂μ ∂timeMeasure H ∂ν)<∞)
    (Z:X→Ω→CircleL2)
    (hZ:∀x,∀ᵐω∂μ,∀l:ℤ,
      (coefficient l (Z x ω)).re=J.integral (r x l) ω ∧
      (coefficient l (Z x ω)).im=J.integral (i x l) ω):
    ∃Y:X×Ω→CircleL2,Measurable Y ∧
      (∀ᵐx∂ν,(fun ω=>Y (x,ω))=ᵐ[μ] Z x) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (‖Y (x,ω)‖^2) ∂μ ∂ν)=
        ∫⁻x,∫⁻ω,ENNReal.ofReal (‖Z x ω‖^2) ∂μ ∂ν:=by
  classical
  choose Yr hYr hYra using fun l=>hF X ν (fun x=>r x l) (R l) (hR l) (fun x=>hr x l) (hRf l)
  choose Yi hYi hYia using fun l=>hF X ν (fun x=>i x l) (I l) (hI l) (fun x=>hi x l) (hIf l)
  let c:X×Ω→ℤ→ℂ:=fun p l=>Complex.mk (Yr l p) (Yi l p)
  have hc:∀l,Measurable (fun p=>c p l):=fun l=>by
    have hm:=((Complex.measurable_ofReal.comp (hYr l)).add
      ((Complex.measurable_ofReal.comp (hYi l)).mul_const Complex.I))
    convert! hm using 1
    funext p
    exact Complex.mk_eq_add_mul_I (Yr l p) (Yi l p)
  let Y:X×Ω→CircleL2:=fun p=>
    (fourierBasis (T:=2*Real.pi)).repr.symm (SquareSeriesField.value c p)
  have hYm:Measurable Y:=(fourierBasis (T:=2*Real.pi)).repr.symm.continuous.measurable.comp
    (SquareSeriesField.value_measurable c hc)
  have hYa:∀ᵐx∂ν,(fun ω=>Y (x,ω))=ᵐ[μ] Z x:=by
    filter_upwards [ae_all_iff.mpr hYra,ae_all_iff.mpr hYia] with x hxR hxI
    filter_upwards [ae_all_iff.mpr hxR,ae_all_iff.mpr hxI,hZ x] with ω hωR hωI hωZ
    have hcoeff:∀l,c (x,ω) l=coefficient l (Z x ω):=by
      intro l
      apply Complex.ext
      · exact (hωR l).trans (hωZ l).1.symm
      · exact (hωI l).trans (hωZ l).2.symm
    have hs:Summable (fun l=>‖c (x,ω) l‖^2):=by
      have ht:=HilbertTrace.basis_sq (fourierBasis (T:=2*Real.pi)) (Z x ω)
      exact ht.1.congr (fun l=>by rw [hcoeff l];rfl)
    apply (fourierBasis (T:=2*Real.pi)).repr.injective
    apply lp.ext
    funext l
    change ((fourierBasis (T:=2*Real.pi)).repr
      ((fourierBasis (T:=2*Real.pi)).repr.symm (SquareSeriesField.value c (x,ω)))) l=_
    rw [LinearIsometryEquiv.apply_symm_apply,SquareSeriesField.value_apply c (x,ω) hs l]
    simpa only [HilbertBasis.repr_apply_apply,coefficient,ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.coe_coe,innerSL_apply_apply] using hcoeff l
  refine ⟨Y,hYm,hYa,?_⟩
  apply lintegral_congr_ae
  filter_upwards [hYa] with x hx
  exact lintegral_congr_ae (hx.fun_comp (fun f=>ENNReal.ofReal (‖f‖^2)))

theorem exists_of_output_energy
    (J:StandardTerminalIto (C:=OrthogonalItoChannels.Both Row) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J)(ν:Measure X)[SFinite ν]
    (r i:X→ℤ→Process (E:=OrthogonalItoChannels.Both Row) 𝓕 μ H)
    (R I:ℤ→X×(ℝ≥0×Ω)→OrthogonalItoChannels.Both Row)
    (hR:∀l,StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] (R l))
    (hI:∀l,StronglyMeasurable[(inferInstance:MeasurableSpace X).prod 𝓕.predictable] (I l))
    (hr:∀x l,r x l=ᵐ[energyMeasure μ H] fun p=>R l (x,p))
    (hi:∀x l,i x l=ᵐ[energyMeasure μ H] fun p=>I l (x,p))
    (Z:X→Ω→CircleL2)
    (hZ:∀x,∀ᵐω∂μ,∀l:ℤ,
      (coefficient l (Z x ω)).re=J.integral (r x l) ω ∧
      (coefficient l (Z x ω)).im=J.integral (i x l) ω)
    (hfinite:(∫⁻x,∫⁻ω,ENNReal.ofReal (‖Z x ω‖^2) ∂μ ∂ν)<∞):
    ∃Y:X×Ω→CircleL2,Measurable Y ∧
      (∀ᵐx∂ν,(fun ω=>Y (x,ω))=ᵐ[μ] Z x) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (‖Y (x,ω)‖^2) ∂μ ∂ν)=
        ∫⁻x,∫⁻ω,ENNReal.ofReal (‖Z x ω‖^2) ∂μ ∂ν:=by
  have hraw (K:Process (E:=OrthogonalItoChannels.Both Row) 𝓕 μ H)
      (G:(ℝ≥0×Ω)→OrthogonalItoChannels.Both Row)(hKG:K=ᵐ[energyMeasure μ H] G):
      (∫⁻t,∫⁻ω,ENNReal.ofReal (‖G (t,ω)‖^2) ∂μ ∂timeMeasure H)=
        ∫⁻ω,ENNReal.ofReal (‖J.integral K ω‖^2) ∂μ:=by
    calc
      _=∫⁻t,∫⁻ω,ENNReal.ofReal (‖K (t,ω)‖^2) ∂μ ∂timeMeasure H:=by
        apply lintegral_congr_ae
        filter_upwards [Measure.ae_ae_of_ae_prod hKG] with t ht
        exact lintegral_congr_ae (ht.mono (fun ω hω=>
          congrArg (fun z=>ENNReal.ofReal (‖z‖^2)) hω.symm))
      _=ENNReal.ofReal (‖J.integral K‖^2):=(J.isometry_energy K).symm
      _=_:=LpEnergy.lintegral_energy _
  have hbound (f:CircleL2)(l:ℤ):
      ENNReal.ofReal (|(coefficient l f).re|^2)≤ENNReal.ofReal (‖f‖^2) ∧
      ENNReal.ofReal (|(coefficient l f).im|^2)≤ENNReal.ofReal (‖f‖^2):=by
    rw [NativeHilbertFourierEnergy.norm_sq_split]
    constructor
    · apply le_trans ?_ (le_add_of_nonneg_right bot_le)
      simpa only [Real.norm_eq_abs] using
        ENNReal.le_tsum (f:=fun j:ℤ=>ENNReal.ofReal (‖(coefficient j f).re‖^2)) l
    · apply le_trans ?_ (le_add_of_nonneg_left bot_le)
      simpa only [Real.norm_eq_abs] using
        ENNReal.le_tsum (f:=fun j:ℤ=>ENNReal.ofReal (‖(coefficient j f).im‖^2)) l
  apply exists_identified J hF ν r i R I hR hI hr hi _ _ Z hZ
  · intro l
    apply lt_of_le_of_lt _ hfinite
    apply lintegral_mono
    intro x
    dsimp only
    rw [hraw (r x l) (fun p=>R l (x,p)) (hr x l)]
    apply lintegral_mono_ae
    filter_upwards [hZ x] with ω hω
    rw [Real.norm_eq_abs,←(hω l).1]
    exact (hbound (Z x ω) l).1
  · intro l
    apply lt_of_le_of_lt _ hfinite
    apply lintegral_mono
    intro x
    dsimp only
    rw [hraw (i x l) (fun p=>I l (x,p)) (hi x l)]
    apply lintegral_mono_ae
    filter_upwards [hZ x] with ω hω
    rw [Real.norm_eq_abs,←(hω l).2]
    exact (hbound (Z x ω) l).2

end SHE.NativeOriginalOutputParameter
