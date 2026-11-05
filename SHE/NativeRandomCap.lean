module

public import SHE.NativeRandomRows
public import SHE.RandomCapAE

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomRows
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeRandomCap_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeRandomCap_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeRandomCap_exponentFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nativeRandomCap_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance nativeRandomCap_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeRandomCap_nativeMeasurable : MeasurableSpace CircleL2 := borel _
local instance nativeRandomCap_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

theorem nativeRow_measurable_cap {F : Ω×HeatCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω) : Measurable (nativeRow F) :=
  CircleNormalization.push.continuous.measurable.comp
    (RandomRowEnergy.row_measurable_cap (unitField_measurable hF) cap (fun ω x=>hb ω _))

theorem nativeRow_ae_cap {F : Ω×HeatCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω) (ω : Ω) :
    (nativeRow F ω : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>F (ω,x) := by
  have hu := RandomRowEnergy.row_ae_cap (unitField_measurable hF) cap (fun ω x=>hb ω _) ω
  have hp := (CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae hu
  filter_upwards [CircleNormalization.push_ae (RandomRowEnergy.row (unitField F) ω),hp] with x hx hy
  change CircleNormalization.push (RandomRowEnergy.row (unitField F) ω) x=F (ω,x)
  rw [hx,hy]
  change F (ω,CircleNormalization.scale 1 (2*π) (NativeHeatSpan.unitCenter x))=F (ω,x)
  rw [NativeHeatSpan.scale_inverse]

/-- Native-period RMS output smoothing for genuinely random inputs.
The sample-dependent cap is used only to prove integrability; the sharp
constant depends solely on the actual correlated RMS heat envelope. -/
theorem expected_dominated_negative_cap_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Ω×HeatCircle→ℂ} (hF : Measurable F) (cap : Ω→ℝ)
    (hcap : Measurable cap) (hcap2 : Integrable (fun ω=>cap ω^2) μ)
    (hb : ∀ ω x,‖F (ω,x)‖≤cap ω)
    {Λ ρ t K : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2)
    (ht : 0<t) (ht1 : t≤1) (hK : 0≤K) (a : HeatCircle)
    (hsharp : ∀ᵐ x ∂haarAddCircle,rms μ F x≤K*‖ProfileVariance.heatPhysical (8*t) a x‖) :
    Integrable (fun ω=>‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2) μ ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2 ∂μ)≤
        GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*K^2 ∧
      (∫ ω,‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2 ∂μ)≤
        GaussianNegativePacket.traceConstant*Λ^(-ρ)*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*K^2 := by
  have hc : 0<NativeHeatSpan.clock t := NativeHeatSpan.clock_pos ht
  have hd : 1≤4*π^2 := by nlinarith [Real.two_le_pi]
  have hc1 : NativeHeatSpan.clock t≤1 :=
    (div_le_one (by positivity : 0<4*π^2)).mpr (ht1.trans hd)
  have hround (x : UnitAddCircle) : NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) x)=x := by
    apply (CircleNormalization.scale 1 (2*π)).injective
    exact NativeHeatSpan.scale_inverse _
  have hs0 := (CircleNormalization.scale_measurePreserving 1 (2*π)).quasiMeasurePreserving.ae hsharp
  have hs : ∀ᵐ x ∂haarAddCircle,RandomRowEnergy.rms μ (unitField F) x≤
      K*‖HeatMarkov.kernel (8*NativeHeatSpan.clock t) (by positivity) (x-NativeHeatSpan.unitCenter a)‖ := by
    filter_upwards [hs0] with x hx
    have he : ‖ProfileVariance.heatPhysical (8*t) a (CircleNormalization.scale 1 (2*π) x)‖=
        ‖HeatMarkov.kernel (8*NativeHeatSpan.clock t) (by positivity) (x-NativeHeatSpan.unitCenter a)‖ := by
      rw [←NativeHeatSpan.kernel_eq_physical (by positivity : 0<8*t)]
      change ‖HeatMarkov.kernel (NativeHeatSpan.clock (8*t)) _
        (NativeHeatSpan.unitCenter (CircleNormalization.scale 1 (2*π) x)-NativeHeatSpan.unitCenter a)‖=_
      have ht8 : NativeHeatSpan.clock (8*t)=8*NativeHeatSpan.clock t := by unfold NativeHeatSpan.clock;ring
      simp only [ht8,hround]
    rw [he] at hx
    exact hx
  have h := RandomRowEnergy.expected_dominated_negative_cap_ae μ (unitField_measurable hF)
    cap hcap hcap2 (fun ω x=>hb ω _) hΛ hρ hρhalf hc hc1 hK (NativeHeatSpan.unitCenter a) hs
  have he (ω : Ω) : ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (nativeRow F ω)‖^2=
      NegativeNash.energy Λ ρ (RandomRowEnergy.row (unitField F) ω) := by
    rw [nativeRow,CircleNormalization.push_bessel_energy hΛ hρ.le,
      NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
  simpa only [he] using h

end SHE.NativeRandomRows
