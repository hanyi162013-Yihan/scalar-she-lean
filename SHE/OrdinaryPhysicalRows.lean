module
public import SHE.OrdinaryNamedIto
public import SHE.OrdinaryPhysicalGradient

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OrdinaryPhysicalRows
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels
open scoped NNReal ENNReal
local instance ordinaryPhysicalRows_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryPhysicalRows_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryPhysicalRows_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryPhysicalRows_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryPhysicalRows_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryPhysicalRows_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

/-- The original finite-Ito rows are the actual separate additive
and rough residual physical Haar rows throughout the strict window. -/
theorem rows_ae {n:ℕ}(Z:Fin n→Observation)(b:ℝ≥0){δ:ℝ}(hδ:0<δ)
    (hgap:∀i,δ≤(Z i).target-(b:ℝ)):
    ∀ᵐz∂energyMeasure μ H,z.1<b→∀i,
      OrdinaryNamedIto.rows m Z b hδ hgap i z=OrdinaryPhysicalGradient.row m Z z i:=by
  let r0:=LocalNativeObservations.rows 𝓕 μ H m.additive_pos m.additive_pos.le
    (OrdinaryNamedIto.additiveField m) stronglyMeasurable_const Z b hδ hgap
  let r1:=LocalNativeObservations.rows 𝓕 μ H m.lower_pos (OrdinaryNamedIto.upper_nonneg m)
    m.coefficient m.coefficient_predictable Z b hδ hgap
  have hblock(i:Fin n):OrdinaryNamedIto.rows m Z b hδ hgap i=ᵐ[energyMeasure μ H]
      (fun z=>WithLp.toLp 2 (r0 i z,r1 i z)):=TwoChannelItoRows.block_ae 𝓕 μ H (r0 i) (r1 i)
  have h0(i:Fin n):r0 i=ᵐ[energyMeasure μ H]
      NativeObservationProcess.integrand m.additive_pos (OrdinaryNamedIto.additiveField m) (Z i).target b (Z i).center:=
    NativeObservationProcess.process_ae 𝓕 μ H m.additive_pos m.additive_pos.le
      (OrdinaryNamedIto.additiveField m) stronglyMeasurable_const
      (show (b:ℝ)<(Z i).target by have hh:=hgap i;linarith) (Z i).center
  have h1(i:Fin n):r1 i=ᵐ[energyMeasure μ H]
      NativeObservationProcess.integrand m.lower_pos m.coefficient (Z i).target b (Z i).center:=
    NativeObservationProcess.process_ae 𝓕 μ H m.lower_pos (OrdinaryNamedIto.upper_nonneg m)
      m.coefficient m.coefficient_predictable
      (show (b:ℝ)<(Z i).target by have hh:=hgap i;linarith) (Z i).center
  filter_upwards [ae_all_iff.mpr hblock,ae_all_iff.mpr h0,ae_all_iff.mpr h1] with z hb h0 h1
  intro hz i
  rw [hb i,h0 i,h1 i]
  have hzi:(z.1:ℝ)<(b:ℝ):=by exact_mod_cast hz
  rw [NativeObservationProcess.integrand_eq m.additive_pos (OrdinaryNamedIto.additiveField m)
    (show (b:ℝ)<(Z i).target by have hh:=hgap i;linarith),
    NativeObservationProcess.integrand_eq m.lower_pos m.coefficient
    (show (b:ℝ)<(Z i).target by have hh:=hgap i;linarith),if_pos hzi,if_pos hzi]
  rfl

end SHE.OrdinaryPhysicalRows
