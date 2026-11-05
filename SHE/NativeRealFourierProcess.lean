module

public import SHE.NativeHilbertFourierEnergy
public import SHE.NativeRealNoise
public import SHE.NativeObservationNaturality
public import SHE.TwoChannelItoRows
public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeRealFourierProcess
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
local instance : SecondCountableTopology StoppedFourier.CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Columns:=borel _
local instance : BorelSpace Columns:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0)
local notation "ν"=>((energyMeasure μ H).trim (predictable_le_product 𝓕))

def realProcess (K:Process (E:=Columns) 𝓕 μ H):Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H:=
  NativeRealNoise.columnsPart.compLp K

theorem realProcess_ae (K:Process (E:=Columns) 𝓕 μ H):
    realProcess 𝓕 μ H K=ᵐ[energyMeasure μ H] (fun p=>NativeRealNoise.columnsPart (K p)):=
  ae_eq_of_ae_eq_trim (NativeRealNoise.columnsPart.coeFn_compLp K)

/-- Real native columns pass to the ORIGINAL Hilbert Ito space and
back exactly, at the actual predictable L2 class. -/
theorem native_real_eq (K:Process (E:=Columns) 𝓕 μ H)
    (hr:∀ᵐp∂energyMeasure μ H,∀q:FiniteHaar.HaarNode,∀ᵐx∂AddCircle.haarAddCircle,(K p q x).im=0):
    NativeHilbertFourierIto.nativeProcess 𝓕 μ H (realProcess 𝓕 μ H K)=K:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [NativeHilbertFourierIto.nativeProcess_ae 𝓕 μ H (realProcess 𝓕 μ H K),
    realProcess_ae 𝓕 μ H K,hr] with p hn hp hr
  rw [hn,hp]
  exact NativeRealNoise.columns_embed_part (K p) hr

variable (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ0:StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
variable (hIJ1:StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J))
local notation "RealP"=>realProcess 𝓕 μ H

include hIJ0 hIJ1 in
/-- Exact physical Hilbert/Fourier energy for any actual real native
column processes. This allows applying the checked SAME-J Gamma bound
without introducing a second stochastic output or an energy hypothesis. -/
theorem physical_energy (K0 K1:Process (E:=Columns) 𝓕 μ H)
    (hr0:∀ᵐp∂energyMeasure μ H,∀q:FiniteHaar.HaarNode,∀ᵐx∂AddCircle.haarAddCircle,(K0 p q x).im=0)
    (hr1:∀ᵐp∂energyMeasure μ H,∀q:FiniteHaar.HaarNode,∀ᵐx∂AddCircle.haarAddCircle,(K1 p q x).im=0):
    (∫⁻ω,ENNReal.ofReal (‖embed (I0.integral (RealP K0) ω+I1.integral (RealP K1) ω)‖^2) ∂μ)=
      (∫⁻ω,(∑'l:ℤ,ENNReal.ofReal (‖J.integral (NativeFourierIto.realInput 𝓕 μ H l K0 K1) ω‖^2))+
        (∑'l:ℤ,ENNReal.ofReal (‖J.integral (NativeFourierIto.imagInput 𝓕 μ H l K0 K1) ω‖^2)) ∂μ):=by
  rw [NativeHilbertFourierEnergy.physical_energy 𝓕 μ H I0 I1 J hIJ0 hIJ1 (RealP K0) (RealP K1),
    native_real_eq 𝓕 μ H K0 hr0,native_real_eq 𝓕 μ H K1 hr1]

end SHE.NativeRealFourierProcess
