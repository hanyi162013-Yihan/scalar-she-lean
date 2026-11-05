module

public import SHE.NativeFourierNoiseRows
public import SHE.CountableSameItoEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SHE.NativeFourierIto
open MeasureTheory PredictableL2 NativeFourierNoiseRows OrthogonalItoChannels
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)

def realInput (l : ℤ) (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    Process (E:=Both Row) 𝓕 μ h:=
  ((left (C:=Row)).toContinuousLinearMap.comp (realRow l)).compLp K0+
    ((right (C:=Row)).toContinuousLinearMap.comp (realRow l)).compLp K1

def imagInput (l : ℤ) (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    Process (E:=Both Row) 𝓕 μ h:=
  ((left (C:=Row)).toContinuousLinearMap.comp (imagRow l)).compLp K0+
    ((right (C:=Row)).toContinuousLinearMap.comp (imagRow l)).compLp K1

theorem realInput_ae (l : ℤ) (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    realInput 𝓕 μ h l K0 K1 =ᵐ[energyMeasure μ h]
      (fun p=>bothReal l (K0 p) (K1 p)) := by
  apply ae_eq_of_ae_eq_trim
  filter_upwards [Lp.coeFn_add
    (((left (C:=Row)).toContinuousLinearMap.comp (realRow l)).compLp K0)
    (((right (C:=Row)).toContinuousLinearMap.comp (realRow l)).compLp K1),
    ((left (C:=Row)).toContinuousLinearMap.comp (realRow l)).coeFn_compLp K0,
    ((right (C:=Row)).toContinuousLinearMap.comp (realRow l)).coeFn_compLp K1] with p hp h0 h1
  dsimp only [realInput]
  rw [hp,Pi.add_apply,h0,h1]
  apply WithLp.ofLp_injective
  ext <;> simp [left,right,bothReal]

theorem imagInput_ae (l : ℤ) (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    imagInput 𝓕 μ h l K0 K1 =ᵐ[energyMeasure μ h]
      (fun p=>bothImag l (K0 p) (K1 p)) := by
  apply ae_eq_of_ae_eq_trim
  filter_upwards [Lp.coeFn_add
    (((left (C:=Row)).toContinuousLinearMap.comp (imagRow l)).compLp K0)
    (((right (C:=Row)).toContinuousLinearMap.comp (imagRow l)).compLp K1),
    ((left (C:=Row)).toContinuousLinearMap.comp (imagRow l)).coeFn_compLp K0,
    ((right (C:=Row)).toContinuousLinearMap.comp (imagRow l)).coeFn_compLp K1] with p hp h0 h1
  dsimp only [imagInput]
  rw [hp,Pi.add_apply,h0,h1]
  apply WithLp.ofLp_injective
  ext <;> simp [left,right,bothImag]

/-- Both real and imaginary Fourier scalar rows of the SAME original
noise have exactly the physical Hilbert-column energy. No second
Hilbert-valued integral or independence assumption is introduced. -/
theorem scalar_energy
    (J : StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ h)
    (K0 K1 : Process (E:=Columns) 𝓕 μ h) :
    (∫⁻ ω, (∑' l : ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ h l K0 K1) ω‖^2))+
      (∑' l : ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ h l K0 K1) ω‖^2)) ∂μ)=
      ∫⁻ p,ENNReal.ofReal (‖K0 p‖^2+‖K1 p‖^2) ∂energyMeasure μ h := by
  rw [lintegral_add_left (Measurable.ennreal_tsum (fun l=>
    CountableSameItoEnergy.scalar_measurable J (realInput 𝓕 μ h l K0 K1))),
    CountableSameItoEnergy.coordinate_energy J,
    CountableSameItoEnergy.coordinate_energy J,
    ←lintegral_add_left (Measurable.ennreal_tsum (fun l=>
      CountableSameItoEnergy.row_measurable (realInput 𝓕 μ h l K0 K1)))]
  apply lintegral_congr_ae
  have hr:=ae_all_iff.mpr (fun l=>realInput_ae 𝓕 μ h l K0 K1)
  have hi:=ae_all_iff.mpr (fun l=>imagInput_ae 𝓕 μ h l K0 K1)
  filter_upwards [hr,hi] with p hp hq
  simp only [hp,hq]
  have ht:=both_trace (K0 p) (K1 p)
  have hs0 : Summable (fun l : ℤ=>‖bothReal l (K0 p) (K1 p)‖^2):=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) (fun _=>le_add_of_nonneg_right (sq_nonneg _)) ht.1
  have hs1 : Summable (fun l : ℤ=>‖bothImag l (K0 p) (K1 p)‖^2):=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) (fun _=>le_add_of_nonneg_left (sq_nonneg _)) ht.1
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _=>sq_nonneg _) hs0,
    ←ENNReal.ofReal_tsum_of_nonneg (fun _=>sq_nonneg _) hs1,
    ←ENNReal.ofReal_add (tsum_nonneg (fun _=>sq_nonneg _)) (tsum_nonneg (fun _=>sq_nonneg _)),
    ←hs0.tsum_add hs1,ht.2]

end SHE.NativeFourierIto
