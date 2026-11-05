module
public import SHE.ParametricStoppedHaarRows
public import SHE.TimeMeasureMass
public import SHE.StandardItoParameterFubini
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.ParametricStoppedHaarEnergy
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier ParametricStoppedHaarRows
open scoped NNReal ENNReal
local instance parametricStoppedHaarEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable {ell M:ℝ}(hell:0<ell)(hM:0≤M)
variable (v b q:X→ℝ≥0)(center:X→HeatCircle)(f:X×(ℝ≥0×Ω)→EllipticField ell M)
variable (hqb:∀x,q x≤b x)(hbH:∀x,b x≤H)(hH:(H:ℝ)≤1)

def constant (M:ℝ)(H:ℝ≥0):ℝ:=M*(1+heatConstant)*(2*Real.sqrt H)
local notation "Raw"=>ParametricStoppedHaarRows.raw hell v b q center f

include 𝓕 hM hqb hbH hH in
/-- True ORIGINAL full-H time/sample energy is uniformly bounded over
all parameters, including endpoint stops q=b and correlated fields. -/
theorem energy_bound (x:X):
    (∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal (constant M H):=by
  let K:ℝ:=M*(1+heatConstant)
  have hK:0≤K:=mul_nonneg hM (by linarith [heatConstant_pos])
  have hb(t:ℝ≥0)(ω:Ω):ENNReal.ofReal (‖Raw (x,(t,ω))‖^2)≤
      ENNReal.ofReal K*(Iio (q x)).indicator
        (fun r:ℝ≥0=>ENNReal.ofReal (((q x:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) t:=by
    have hh:=ParametricStoppedHaarRows.raw_norm_sq hell hM v b q center f hqb x (t,ω)
    by_cases ht:t<q x
    · rw [Set.indicator_of_mem (show t∈Iio (q x) from ht)] at hh ⊢
      have ha:0<(q x:ℝ)-(t:ℝ):=sub_pos.mpr (by exact_mod_cast ht)
      have ha1:(q x:ℝ)-(t:ℝ)≤1:=by
        have hqH: (q x:ℝ)≤H:=NNReal.coe_le_coe.mpr ((hqb x).trans (hbH x))
        linarith [t.coe_nonneg]
      have hp:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by norm_num:-(1/2:ℝ)≤0)
      rw [←ENNReal.ofReal_mul hK]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [K]
      nlinarith [heatConstant_pos,Real.rpow_nonneg ha.le (-(1/2:ℝ))]
    · rw [Set.indicator_of_notMem (show t∉Iio (q x) from ht)] at hh ⊢
      simpa only [mul_zero,ENNReal.ofReal_zero] using ENNReal.ofReal_le_ofReal hh
  have he:(∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw (x,(t,ω))‖^2) ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal K*ENNReal.ofReal (2*Real.sqrt (q x)):=by
    calc
      _≤∫⁻t,ENNReal.ofReal K*(Iio (q x)).indicator
          (fun r:ℝ≥0=>ENNReal.ofReal (((q x:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) t ∂timeMeasure H:=by
        apply lintegral_mono
        intro t
        calc
          _≤∫⁻_:Ω,ENNReal.ofReal K*(Iio (q x)).indicator
              (fun r:ℝ≥0=>ENNReal.ofReal (((q x:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) t ∂μ:=lintegral_mono (hb t)
          _=_:=by simp
      _=_:=by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Iio,
          NativeStoppedBracket.timeMeasure_before ((hqb x).trans (hbH x)),
          causal_rpow_mass (by norm_num : (-1:ℝ) < -(1/2:ℝ))]
        norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
        rw [Real.sqrt_eq_rpow]
        congr 2
        ring
  calc
    _≤ENNReal.ofReal K*ENNReal.ofReal (2*Real.sqrt (q x)):=he
    _≤ENNReal.ofReal K*ENNReal.ofReal (2*Real.sqrt H):=by
      gcongr
      exact_mod_cast (hqb x).trans (hbH x)
    _=_:=by rw [←ENNReal.ofReal_mul hK];rfl

end SHE.ParametricStoppedHaarEnergy
