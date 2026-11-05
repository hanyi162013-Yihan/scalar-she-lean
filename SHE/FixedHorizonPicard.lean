module

public import SHE.WeightedDampedIsometry
public import SHE.BieleckiColumnEnergy
public import SHE.DampedNonlinearConvolution
public import SHE.PredictableExponential
public import SHE.DampedStochasticConvolution
public import SHE.NonlinearConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FixedHorizonPicard
open MeasureTheory Set PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (h : ℝ≥0) (hh : (h:ℝ) ≤ 1)
variable {Λ : ℝ} (hΛ : 0 ≤ Λ)
variable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
variable (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hβ : 0 < β) (hH : 0 ≤ H) (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)

variable(I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ h)
variable(B:ℝ≥0)(hBDG:StandardTerminalBDG16 I B)(hpos:0<h)
local notation "N"=>DampedNonlinearConvolution.map 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I
local notation "Scale"=>PredictableExponential.scale 𝓕 μ h

include hBDG hpos in
theorem weighted_isometry(γ:ℝ)(u v:Process (E:=StateL2) 𝓕 μ h):
    ENNReal.ofReal (‖Scale (-γ) (N u-N v)‖^2)=
      ∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*
        (Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
          CompanionHeat.columnEnergy a ha M (absBound hell hb) (u (s,ω)) (v (s,ω)) ((t:ℝ)-(s:ℝ))))
        ∂μ ∂timeMeasure t ∂timeMeasure h:=by
  rw [DampedNonlinearConvolution.map,DampedNonlinearConvolution.map,
    WeightedDampedIsometry.weighted_energy 𝓕 μ h hh hΛ hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2)) _ _ _ _ I hpos B hBDG γ]
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem h] with t ht
  apply lintegral_congr_ae
  filter_upwards [timeMeasure_ae_mem t,(timeMeasure t).ae_ne t] with s hs hst
  have hτ:0<(t:ℝ)-(s:ℝ):=sub_pos.mpr (by exact_mod_cast lt_of_le_of_ne hs.2 hst)
  apply lintegral_congr
  intro ω
  change ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*(Real.exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
    ‖NonlinearHaarIntegrand.kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),u (s,ω))-
      NonlinearHaarIntegrand.kernel a ha ell M hell hb ((t:ℝ)-(s:ℝ),v (s,ω))‖^2))=_
  rw [NonlinearHaarIntegrand.kernel_difference_norm_sq ha hell hb hτ]

include hBDG hpos in
theorem weighted_bound {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))
    {γ:ℝ}(hγ:0<γ)(u v:Process (E:=StateL2) 𝓕 μ h):
    ENNReal.ofReal (‖Scale (-γ) (N u-N v)‖^2)≤
      ENNReal.ofReal (CompanionHeat.picardConstant ell M L*BieleckiKernel.mass γ)*
        ENNReal.ofReal (‖Scale (-γ) (u-v)‖^2):=by
  rw [weighted_isometry 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I B hBDG hpos γ]
  have hu:Measurable (fun p:ℝ≥0×Ω=>u p):=
    (realization_stronglyMeasurable (energyMeasure μ h) (predictable_le_product 𝓕) u).measurable
  have hv:Measurable (fun p:ℝ≥0×Ω=>v p):=
    (realization_stronglyMeasurable (energyMeasure μ h) (predictable_le_product 𝓕) v).measurable
  have he:=BieleckiColumnEnergy.expected_energy μ ha hell hb (absBound hell hb) hLip h hh u v hu hv hΛ hγ
  apply he.trans_eq
  congr 1
  rw [PredictableExponential.energy]
  have hs:=Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v))
  apply lintegral_congr_ae
  filter_upwards [hs] with s hs
  apply lintegral_congr_ae
  filter_upwards [hs] with ω hω
  rw [hω]
  congr 3
  ring

include hBDG hpos in
/-- The actual forced stochastic equation has a unique predictable-L2
solution on every prescribed positive h≤1. The Bielecki exponent may
depend on the Lipschitz constant; the interval does not. -/
theorem exists_unique_forced {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))
    (forcing:Process (E:=StateL2) 𝓕 μ h):
    ∃!v:Process (E:=StateL2) 𝓕 μ h,v=forcing+N v:=by
  obtain ⟨γ,hγ,hsmall⟩:=BieleckiKernel.exists_contraction_weight (CompanionHeat.picardConstant ell M L)
  have hγpos:0<γ:=lt_of_lt_of_le zero_lt_one hγ
  apply PredictableExponential.exists_unique 𝓕 μ h γ forcing N
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he:=weighted_bound 𝓕 μ h hh hΛ ha hell hb hβ hH hholder I B hBDG hpos hLip hγpos
    (Scale γ u) (Scale γ v)
  have hs:Scale (-γ) (Scale γ u-Scale γ v)=u-v:=by
    rw [←PredictableExponential.sub,PredictableExponential.cancel]
  have hC:0≤CompanionHeat.picardConstant ell M L*BieleckiKernel.mass γ:=mul_nonneg
    (CompanionHeat.picardConstant_nonneg (hell.le.trans ((hb 0).1.trans (hb 0).2)) L)
    (BieleckiKernel.mass_nonneg hγpos.le)
  rw [hs,←ENNReal.ofReal_mul hC] at he
  have hreal:‖Scale (-γ) (N (Scale γ u)-N (Scale γ v))‖^2≤(1/4:ℝ)*‖u-v‖^2:=
    ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).mp he).trans
      (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))
  have hd:PredictableExponential.conjugate 𝓕 μ h γ forcing N u-
      PredictableExponential.conjugate 𝓕 μ h γ forcing N v=
      Scale (-γ) (N (Scale γ u)-N (Scale γ v)):=by
    rw [PredictableExponential.conjugate,PredictableExponential.conjugate,
      ←PredictableExponential.sub,add_sub_add_left_eq_sub]
  rw [dist_eq_norm,dist_eq_norm,hd]
  change ‖Scale (-γ) (N (Scale γ u)-N (Scale γ v))‖≤(1/2:ℝ)*‖u-v‖
  nlinarith [norm_nonneg (Scale (-γ) (N (Scale γ u)-N (Scale γ v))),norm_nonneg (u-v)]

end SHE.FixedHorizonPicard
