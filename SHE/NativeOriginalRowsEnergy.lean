module
public import SHE.NativeHilbertFourierEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeOriginalRowsEnergy
open MeasureTheory PredictableL2 NativeFourierNoiseRows NativeHilbertFourierEnergy
open scoped ENNReal NNReal
variable {Ω:Type*}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[SFinite μ]{H:ℝ≥0}

/-- Original scalar input rows determine the native Hilbert output
energy exactly. Only the checked coordinate identities are needed;
no extra Hilbert stochastic integral or predictable-version choice is
introduced for the native column field. -/
theorem identified_energy (J:StandardTerminalIto (C:=OrthogonalItoChannels.Both Row) (E:=ℝ) 𝓕 μ H)
    (r i:ℤ→Process (E:=OrthogonalItoChannels.Both Row) 𝓕 μ H)
    (Y:Ω→StoppedFourier.CircleL2)(K0 K1:(ℝ≥0×Ω)→Columns)
    (hY:∀ᵐω∂μ,∀l:ℤ,
      (coefficient l (Y ω)).re=J.integral (r l) ω ∧
      (coefficient l (Y ω)).im=J.integral (i l) ω)
    (hr:∀l:ℤ,r l=ᵐ[energyMeasure μ H] fun p=>bothReal l (K0 p) (K1 p))
    (hi:∀l:ℤ,i l=ᵐ[energyMeasure μ H] fun p=>bothImag l (K0 p) (K1 p)):
    (∫⁻ω,ENNReal.ofReal (‖Y ω‖^2) ∂μ)=
      ∫⁻p,ENNReal.ofReal (‖K0 p‖^2+‖K1 p‖^2) ∂energyMeasure μ H:=by
  have hout:(∫⁻ω,ENNReal.ofReal (‖Y ω‖^2) ∂μ)=
      ∫⁻ω,(∑'l:ℤ,ENNReal.ofReal (‖J.integral (r l) ω‖^2))+
        (∑'l:ℤ,ENNReal.ofReal (‖J.integral (i l) ω‖^2)) ∂μ:=by
    apply lintegral_congr_ae
    filter_upwards [hY] with ω hω
    rw [norm_sq_split]
    congr 1
    · exact tsum_congr (fun l=>by rw [(hω l).1])
    · exact tsum_congr (fun l=>by rw [(hω l).2])
  rw [hout,lintegral_add_left (Measurable.ennreal_tsum (fun l=>CountableSameItoEnergy.scalar_measurable J (r l))),
    CountableSameItoEnergy.coordinate_energy J,CountableSameItoEnergy.coordinate_energy J,
    ←lintegral_add_left (Measurable.ennreal_tsum (fun l=>CountableSameItoEnergy.row_measurable (r l)))]
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr hr,ae_all_iff.mpr hi] with p hr hi
  simp only [hr,hi]
  have ht:=both_trace (K0 p) (K1 p)
  have hs0:Summable (fun l:ℤ=>‖bothReal l (K0 p) (K1 p)‖^2):=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) (fun _=>le_add_of_nonneg_right (sq_nonneg _)) ht.1
  have hs1:Summable (fun l:ℤ=>‖bothImag l (K0 p) (K1 p)‖^2):=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) (fun _=>le_add_of_nonneg_left (sq_nonneg _)) ht.1
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _=>sq_nonneg _) hs0,
    ←ENNReal.ofReal_tsum_of_nonneg (fun _=>sq_nonneg _) hs1,
    ←ENNReal.ofReal_add (tsum_nonneg (fun _=>sq_nonneg _)) (tsum_nonneg (fun _=>sq_nonneg _)),
    ←hs0.tsum_add hs1,ht.2]

end SHE.NativeOriginalRowsEnergy
