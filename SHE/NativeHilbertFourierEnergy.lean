module

public import SHE.NativeHilbertFourierIto
public import SHE.NativeObservationNaturality
public import SHE.TwoChannelItoRows
public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeHilbertFourierEnergy
open MeasureTheory PredictableL2 NativeObservationNaturality NativeHeatObservation DyadicApproximation FiniteHaar
open OrthogonalItoChannels NativeFourierNoiseRows
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
local notation "ν"=>((energyMeasure μ H).trim (predictable_le_product 𝓕))

/-- Exact Parseval with both real and imaginary output coefficients. -/
theorem norm_sq_split (f:StoppedFourier.CircleL2):
    ENNReal.ofReal (‖f‖^2)=
      (∑'l:ℤ,ENNReal.ofReal (‖(coefficient l f).re‖^2))+
        (∑'l:ℤ,ENNReal.ofReal (‖(coefficient l f).im‖^2)):=by
  have ht:=HilbertTrace.basis_sq (_root_.fourierBasis (T:=2*Real.pi)) f
  change Summable (fun l:ℤ=>‖coefficient l f‖^2) ∧ (∑'l:ℤ,‖coefficient l f‖^2)=‖f‖^2 at ht
  have hp(l:ℤ):‖(coefficient l f).re‖^2+‖(coefficient l f).im‖^2=‖coefficient l f‖^2:=by
    rw [Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs,Complex.sq_norm,Complex.normSq_apply]
    ring
  have hr:Summable (fun l:ℤ=>‖(coefficient l f).re‖^2):=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) (fun l=>by rw [←hp l];exact le_add_of_nonneg_right (sq_nonneg _)) ht.1
  have hi:Summable (fun l:ℤ=>‖(coefficient l f).im‖^2):=
    Summable.of_nonneg_of_le (fun _=>sq_nonneg _) (fun l=>by rw [←hp l];exact le_add_of_nonneg_left (sq_nonneg _)) ht.1
  symm
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _=>sq_nonneg _) hr,
    ←ENNReal.ofReal_tsum_of_nonneg (fun _=>sq_nonneg _) hi,
    ←ENNReal.ofReal_add (tsum_nonneg (fun _=>sq_nonneg _)) (tsum_nonneg (fun _=>sq_nonneg _)),
    ←hr.tsum_add hi]
  exact congrArg ENNReal.ofReal ((tsum_congr hp).trans ht.2)

variable (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ0:StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
variable (hIJ1:StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J))
local notation "Native"=>NativeHilbertFourierIto.nativeProcess 𝓕 μ H

include hIJ0 hIJ1 in
/-- The actual original Hilbert stochastic output and the SAME-J full
Fourier output have EXACTLY equal energy, not just a parallel estimate.
Only ordinary scalar naturality and Parseval are used. -/
theorem physical_energy (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    (∫⁻ω,ENNReal.ofReal (‖embed (I0.integral K0 ω+I1.integral K1 ω)‖^2) ∂μ)=
      (∫⁻ω,(∑'l:ℤ,ENNReal.ofReal (‖J.integral (NativeFourierIto.realInput 𝓕 μ H l (Native K0) (Native K1)) ω‖^2))+
        (∑'l:ℤ,ENNReal.ofReal (‖J.integral (NativeFourierIto.imagInput 𝓕 μ H l (Native K0) (Native K1)) ω‖^2)) ∂μ):=by
  apply lintegral_congr_ae
  filter_upwards [NativeHilbertFourierIto.coefficients 𝓕 μ H I0 I1 J hIJ0 hIJ1 K0 K1] with ω hω
  rw [norm_sq_split]
  congr 1
  · exact tsum_congr (fun l=>by rw [(hω l).1])
  · exact tsum_congr (fun l=>by rw [(hω l).2])

include hIJ0 hIJ1 in
/-- Exact source energy for the actual physical Hilbert stochastic
output. This identifies the scalar Fourier isometry with the physical
field constructed using the user's original two Hilbert Ito maps. -/
theorem source_energy (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    (∫⁻ω,ENNReal.ofReal (‖embed (I0.integral K0 ω+I1.integral K1 ω)‖^2) ∂μ)=
      ∫⁻p,ENNReal.ofReal (‖Native K0 p‖^2+‖Native K1 p‖^2) ∂energyMeasure μ H:=by
  rw [physical_energy 𝓕 μ H I0 I1 J hIJ0 hIJ1 K0 K1]
  exact NativeFourierIto.scalar_energy 𝓕 μ H J (Native K0) (Native K1)

end SHE.NativeHilbertFourierEnergy
