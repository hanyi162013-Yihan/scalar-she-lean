module
public import SHE.DampedPredictableVersion
public import SHE.PredictableExponential
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.WeightedDampedIsometry
open MeasureTheory Set PredictableL2 CircleHeat FiniteHaar
open scoped ENNReal NNReal
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
local instance : MeasurableSpace LowBands.StateL2:=borel _
local instance : BorelSpace LowBands.StateL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(h:ℝ≥0)(hh:(h:ℝ)≤1){Λ ell M:ℝ}(hΛ:0≤Λ)(hell:0<ell)(hM:0≤M)
variable(f g:ℝ≥0×Ω→EllipticField ell M)
variable(hf:StronglyMeasurable[𝓕.predictable] f)(hg:StronglyMeasurable[𝓕.predictable] g)
variable(I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=LowBands.StateL2) 𝓕 μ h)

private theorem lp_difference_energy (U V:Lp LowBands.StateL2 2 μ):
    ENNReal.ofReal (‖U-V‖^2)=∫⁻ω,ENNReal.ofReal (‖U ω-V ω‖^2) ∂μ:=by
  rw [realLp_norm_sq,ofReal_integral_eq_lintegral_ofReal
    (Lp.memLp (U-V)).norm.integrable_sq (ae_of_all _ (fun _=>sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub U V] with ω hω
  rw [hω]
  rfl

/-- Exact same-integral energy at a fixed terminal time, with the
original full-horizon input support restricted to its true causal window. -/
theorem fixed_energy(t:ℝ≥0)(ht:t≤h):
    (∫⁻ω,ENNReal.ofReal (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t ht ω-
      DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM g hg I t ht ω‖^2) ∂μ)=
      ∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
        ‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))-
          RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2)
        ∂μ ∂timeMeasure t:=by
  let uf:=DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM f hf t ht
  let ug:=DampedFixedIntegral.input 𝓕 μ h hh hΛ hell hM g hg t ht
  have he:=I.difference_energy uf ug
  rw [lp_difference_energy μ] at he
  change (∫⁻ω,ENNReal.ofReal (‖I.integral uf ω-I.integral ug ω‖^2) ∂μ)=_
  calc
    _=∫⁻s,∫⁻ω,ENNReal.ofReal (‖uf (s,ω)-ug (s,ω)‖^2) ∂μ ∂timeMeasure h:=he
    _=∫⁻s,∫⁻ω,ENNReal.ofReal (‖DampedKernelModel.raw (Λ:=Λ) hell f (t,(s,ω))-
        DampedKernelModel.raw (Λ:=Λ) hell g (t,(s,ω))‖^2) ∂μ ∂timeMeasure h:=by
      have hae:=Measure.ae_ae_of_ae_prod ((DampedFixedIntegral.input_ae 𝓕 μ h hh hΛ hell hM f hf t ht).prodMk
        (DampedFixedIntegral.input_ae 𝓕 μ h hh hΛ hell hM g hg t ht))
      apply lintegral_congr_ae
      filter_upwards [hae] with s hs
      apply lintegral_congr_ae
      filter_upwards [hs] with ω hω
      have hω:=Prod.mk.inj hω
      rw [hω.1,hω.2]
      rfl
    _=∫⁻s,∫⁻ω,ENNReal.ofReal (‖DampedKernelModel.raw (Λ:=Λ) hell f (t,(s,ω))-
        DampedKernelModel.raw (Λ:=Λ) hell g (t,(s,ω))‖^2) ∂μ ∂timeMeasure t:=
      DampedStochasticConvolution.causal_pair_lintegral hell μ f g ht
    _=_:=by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro ω
      rw [DampedKernelModel.raw,DampedKernelModel.raw,DampedStochasticConvolution.kernel_difference_norm_sq]

local notation "Cf"=>DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I f hf
local notation "Cg"=>DampedStochasticConvolution.convolution 𝓕 μ h hh hΛ hell hM I g hg

/-- Weighted stochastic convolution isometry, proved for the actual
constructed predictable convolution using its checked continuous version
and the original terminal Itô isometry. No convolution-map premise. -/
theorem weighted_energy(hpos:0<h)(B:ℝ≥0)(hBDG:StandardTerminalBDG16 I B)(γ:ℝ):
    ENNReal.ofReal (‖PredictableExponential.scale 𝓕 μ h (-γ) (Cf-Cg)‖^2)=
      ∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
        (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
          ‖RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))-
            RealHaarIntegrand.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2))
        ∂μ ∂timeMeasure t ∂timeMeasure h:=by
  rw [PredictableExponential.energy]
  have hfv:=Measure.ae_ae_of_ae_prod (DampedPredictableVersion.convolution_ae_version
    𝓕 μ h hh hΛ hell hM f hf I B hBDG hpos)
  have hgv:=Measure.ae_ae_of_ae_prod (DampedPredictableVersion.convolution_ae_version
    𝓕 μ h hh hΛ hell hM g hg I B hBDG hpos)
  have hsub:=Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub Cf Cg))
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h,hfv,hgv,hsub] with t ht hft hgt hst
  have htf:(fun ω=>Cf (t,ω))=ᵐ[μ] DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t ht.2:=by
    filter_upwards [hft,DampedContinuousVersion.version_ae_of_le 𝓕 μ h hh hΛ hell hM f hf I B hBDG hpos t ht.2] with ω hω hv
    exact hω.trans hv
  have htg:(fun ω=>Cg (t,ω))=ᵐ[μ] DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM g hg I t ht.2:=by
    filter_upwards [hgt,DampedContinuousVersion.version_ae_of_le 𝓕 μ h hh hΛ hell hM g hg I B hBDG hpos t ht.2] with ω hω hv
    exact hω.trans hv
  calc
    _=∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
      ‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t ht.2 ω-
        DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM g hg I t ht.2 ω‖^2) ∂μ:=by
      apply lintegral_congr_ae
      filter_upwards [htf,htg,hst] with ω hfω hgω hsω
      simp only [Pi.sub_apply] at hsω
      rw [hsω,hfω,hgω]
      congr 3
      ring
    _=ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ)))*
      (∫⁻ω,ENNReal.ofReal (‖DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM f hf I t ht.2 ω-
        DampedFixedIntegral.value 𝓕 μ h hh hΛ hell hM g hg I t ht.2 ω‖^2) ∂μ):=by
      simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _=_:=by
      rw [fixed_energy 𝓕 μ h hh hΛ hell hM f g hf hg I t ht.2]
      simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end SHE.WeightedDampedIsometry
