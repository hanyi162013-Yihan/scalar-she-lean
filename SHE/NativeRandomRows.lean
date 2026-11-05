module

public import SHE.RandomNegativeRows
public import SHE.NativeHeatConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomRows
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeRandomRows_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeRandomRows_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeRandomRows_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeRandomRows_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeRandomRows_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeRandomRows_nativeMeasurable : MeasurableSpace StoppedFourier.CircleL2 := borel StoppedFourier.CircleL2
local instance nativeRandomRows_nativeBorel : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def unitField (F : Ω × HeatCircle → ℂ) (p : Ω × UnitAddCircle) : ℂ :=
  F (p.1,CircleNormalization.scale 1 (2*π) p.2)

def nativeRow (F : Ω × HeatCircle → ℂ) (ω : Ω) : StoppedFourier.CircleL2 :=
  CircleNormalization.push (RandomRowEnergy.row (unitField F) ω)

def rms (F : Ω × HeatCircle → ℂ) (x : HeatCircle) : ℝ :=
  ProfileL2.normTwo μ (fun ω => ‖F (ω,x)‖)

theorem unitField_measurable {F : Ω × HeatCircle → ℂ} (hF : Measurable F) : Measurable (unitField F) :=
  hF.comp (measurable_fst.prodMk ((CircleNormalization.continuous_scale 1 (2*π)).measurable.comp measurable_snd))

theorem nativeRow_measurable {F : Ω × HeatCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) : Measurable (nativeRow F) :=
  CircleNormalization.push.continuous.measurable.comp
    (RandomRowEnergy.row_measurable (unitField_measurable hF) (fun ω x => hb ω _))

/-- The native row is the exact L² class of the supplied physical scalar
field, with normalized Haar measure and no discarded clock factor. -/
theorem nativeRow_ae {F : Ω × HeatCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B) (ω : Ω) :
    (nativeRow F ω : HeatCircle → ℂ)=ᵐ[haarAddCircle] fun x => F (ω,x) := by
  have hunit := RandomRowEnergy.row_ae (unitField_measurable hF) (fun ω x => hb ω _) ω
  have hp := (CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae hunit
  filter_upwards [CircleNormalization.push_ae (RandomRowEnergy.row (unitField F) ω),hp] with x hx hy
  change CircleNormalization.push (RandomRowEnergy.row (unitField F) ω) x=F (ω,x)
  rw [hx,hy]
  change F (ω,CircleNormalization.scale 1 (2*π) (NativeHeatSpan.unitCenter x))=F (ω,x)
  rw [NativeHeatSpan.scale_inverse]

/-- Native-period expected negative-output row energy from the genuine
physical RMS heat envelope. The exact time conversion `t/(4π²)` remains
visible, and the energy is the actual native massive Bessel operator. -/
theorem expected_dominated_negative
    {F : Ω × HeatCircle → ℂ} (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω x, ‖F (ω,x)‖ ≤ B)
    {Λ ρ t K : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 ≤ K) (a : HeatCircle)
    (hsharp : ∀ x, rms μ F x ≤ K*‖ProfileVariance.heatPhysical (8*t) a x‖) :
    Integrable (fun ω => ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2) μ ∧
      (∫ ω, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2 ∂μ) ≤
        GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*K^2 ∧
      (∫ ω, ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2 ∂μ) ≤
        GaussianNegativePacket.traceConstant*Λ^(-ρ)*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*K^2 := by
  have hclock : 0 < NativeHeatSpan.clock t := NativeHeatSpan.clock_pos ht
  have hden : 1 ≤ 4*π^2 := by nlinarith [Real.two_le_pi]
  have hclock1 : NativeHeatSpan.clock t ≤ 1 :=
    (div_le_one (by positivity : 0 < 4*π^2)).mpr (ht1.trans hden)
  have hround (x : UnitAddCircle) : NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) x)=x := by
    apply (CircleNormalization.scale 1 (2*π)).injective
    exact NativeHeatSpan.scale_inverse _
  have hs (x : UnitAddCircle) : RandomRowEnergy.rms μ (unitField F) x ≤
      K*‖HeatMarkov.kernel (8*NativeHeatSpan.clock t) (by positivity) (x-NativeHeatSpan.unitCenter a)‖ := by
    have hh := hsharp (CircleNormalization.scale 1 (2*π) x)
    have he : ‖ProfileVariance.heatPhysical (8*t) a (CircleNormalization.scale 1 (2*π) x)‖=
        ‖HeatMarkov.kernel (8*NativeHeatSpan.clock t) (by positivity) (x-NativeHeatSpan.unitCenter a)‖ := by
      rw [← NativeHeatSpan.kernel_eq_physical (by positivity : 0 < 8*t)]
      change ‖HeatMarkov.kernel (NativeHeatSpan.clock (8*t)) _
        (NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) x)-NativeHeatSpan.unitCenter a)‖=_
      have ht8 : NativeHeatSpan.clock (8*t)=8*NativeHeatSpan.clock t := by unfold NativeHeatSpan.clock; ring
      simp only [ht8,hround]
    rw [he] at hh
    exact hh
  have h := RandomRowEnergy.expected_dominated_negative μ (unitField_measurable hF) hB
    (fun ω x => hb ω _) hΛ hρ hρhalf hclock hclock1 hK (NativeHeatSpan.unitCenter a) hs
  have he (ω : Ω) : ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2=
      NegativeNash.energy Λ ρ (RandomRowEnergy.row (unitField F) ω) := by
    rw [nativeRow,CircleNormalization.push_bessel_energy hΛ hρ.le,
      NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
  simpa only [he] using h

end SHE.NativeRandomRows
