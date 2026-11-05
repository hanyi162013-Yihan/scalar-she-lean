module

public import SHE.NativeFourierIto
public import SHE.NativeObservationNaturality
public import SHE.TwoChannelItoRows
public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeHilbertFourierIto
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

def nativeProcess (K:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):Process (E:=Columns) 𝓕 μ H:=
  (HilbertColumns.mapCLM embed).compLp K

theorem nativeProcess_ae (K:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    nativeProcess 𝓕 μ H K=ᵐ[energyMeasure μ H] (fun p=>HilbertColumns.mapCLM embed (K p)):=
  ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM embed).coeFn_compLp K)

def projectedInput (L:StoppedFourier.CircleL2→L[ℝ]ℝ)
    (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):Process (E:=Both RealHaarInput) 𝓕 μ H:=
  TwoChannelItoRows.block 𝓕 μ H ((HilbertColumns.mapCLM (L.comp embed)).compLp K0)
    ((HilbertColumns.mapCLM (L.comp embed)).compLp K1)

variable (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ0:StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
variable (hIJ1:StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J))

include hIJ0 hIJ1 in
/-- The actual original Hilbert-valued two-channel integral has exactly
its scalar projection in the SAME J; this is ordinary naturality only. -/
theorem projected_integral (L:StoppedFourier.CircleL2→L[ℝ]ℝ)
    (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    (fun ω=>L (embed (I0.integral K0 ω+I1.integral K1 ω)))=ᵐ[μ]
      J.integral (projectedInput 𝓕 μ H L K0 K1):=by
  let Lr:=L.comp embed
  let R0:Process (E:=RealHaarInput) 𝓕 μ H:=(HilbertColumns.mapCLM Lr).compLp K0
  let R1:Process (E:=RealHaarInput) 𝓕 μ H:=(HilbertColumns.mapCLM Lr).compLp K1
  have h0:=Lr.coeFn_compLpL (I0.integral K0)
  have h1:=Lr.coeFn_compLpL (I1.integral K1)
  rw [hIJ0.commutes Lr K0] at h0
  rw [hIJ1.commutes Lr K1] at h1
  have hs:=Lp.coeFn_add ((leftIntegral 𝓕 μ H J).integral R0) ((rightIntegral 𝓕 μ H J).integral R1)
  rw [←TwoChannelItoRows.integral_block 𝓕 μ H J R0 R1] at hs
  filter_upwards [h0,h1,hs] with ω h0 h1 hs
  change Lr (I0.integral K0 ω+I1.integral K1 ω)=J.integral (TwoChannelItoRows.block 𝓕 μ H R0 R1) ω
  rw [map_add,←h0,←h1,hs]
  rfl

theorem real_input (l:ℤ) (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    NativeFourierIto.realInput 𝓕 μ H l (nativeProcess 𝓕 μ H K0) (nativeProcess 𝓕 μ H K1)=
      projectedInput 𝓕 μ H (Complex.reCLM.comp (coefficient l)) K0 K1:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  let L:RealL2→L[ℝ]ℝ:=(Complex.reCLM.comp (coefficient l)).comp embed
  have h0:=ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLp K0)
  have h1:=ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLp K1)
  filter_upwards [NativeFourierIto.realInput_ae 𝓕 μ H l (nativeProcess 𝓕 μ H K0) (nativeProcess 𝓕 μ H K1),
    TwoChannelItoRows.block_ae 𝓕 μ H ((HilbertColumns.mapCLM L).compLp K0) ((HilbertColumns.mapCLM L).compLp K1),
    nativeProcess_ae 𝓕 μ H K0,nativeProcess_ae 𝓕 μ H K1,h0,h1] with p hp hb hn0 hn1 h0 h1
  change _=TwoChannelItoRows.block 𝓕 μ H ((HilbertColumns.mapCLM L).compLp K0) ((HilbertColumns.mapCLM L).compLp K1) p
  rw [hp,hb,hn0,hn1,h0,h1]
  apply WithLp.ofLp_injective
  congr 1

theorem imag_input (l:ℤ) (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    NativeFourierIto.imagInput 𝓕 μ H l (nativeProcess 𝓕 μ H K0) (nativeProcess 𝓕 μ H K1)=
      projectedInput 𝓕 μ H (Complex.imCLM.comp (coefficient l)) K0 K1:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  let L:RealL2→L[ℝ]ℝ:=(Complex.imCLM.comp (coefficient l)).comp embed
  have h0:=ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLp K0)
  have h1:=ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLp K1)
  filter_upwards [NativeFourierIto.imagInput_ae 𝓕 μ H l (nativeProcess 𝓕 μ H K0) (nativeProcess 𝓕 μ H K1),
    TwoChannelItoRows.block_ae 𝓕 μ H ((HilbertColumns.mapCLM L).compLp K0) ((HilbertColumns.mapCLM L).compLp K1),
    nativeProcess_ae 𝓕 μ H K0,nativeProcess_ae 𝓕 μ H K1,h0,h1] with p hp hb hn0 hn1 h0 h1
  change _=TwoChannelItoRows.block 𝓕 μ H ((HilbertColumns.mapCLM L).compLp K0) ((HilbertColumns.mapCLM L).compLp K1) p
  rw [hp,hb,hn0,hn1,h0,h1]
  apply WithLp.ofLp_injective
  congr 1

include hIJ0 hIJ1 in
/-- Every true physical Fourier coefficient uses the same original
noise integral as the checked six-slot Fourier energy bound. -/
theorem coefficients (K0 K1:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    ∀ᵐω∂μ,∀l:ℤ,
      (coefficient l (embed (I0.integral K0 ω+I1.integral K1 ω))).re=
        J.integral (NativeFourierIto.realInput 𝓕 μ H l (nativeProcess 𝓕 μ H K0) (nativeProcess 𝓕 μ H K1)) ω ∧
      (coefficient l (embed (I0.integral K0 ω+I1.integral K1 ω))).im=
        J.integral (NativeFourierIto.imagInput 𝓕 μ H l (nativeProcess 𝓕 μ H K0) (nativeProcess 𝓕 μ H K1)) ω:=by
  have hr(l:ℤ):=(projected_integral 𝓕 μ H I0 I1 J hIJ0 hIJ1 (Complex.reCLM.comp (coefficient l)) K0 K1)
  have hi(l:ℤ):=(projected_integral 𝓕 μ H I0 I1 J hIJ0 hIJ1 (Complex.imCLM.comp (coefficient l)) K0 K1)
  filter_upwards [ae_all_iff.mpr hr,ae_all_iff.mpr hi] with ω hr hi l
  constructor
  · simpa only [real_input,ContinuousLinearMap.comp_apply,Complex.reCLM_apply] using hr l
  · simpa only [imag_input,ContinuousLinearMap.comp_apply,Complex.imCLM_apply] using hi l

end SHE.NativeHilbertFourierIto
