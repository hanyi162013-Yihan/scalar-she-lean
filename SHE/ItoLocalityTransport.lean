module
public import SHE.StandardTerminalPastLocality
public import SHE.HilbertItoNaturality
public import SHE.OrthogonalItoChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.ItoLocalityTransport
open Set MeasureTheory PredictableL2 PastItoInputs PredictableItoRotation
open scoped NNReal ENNReal
variable {Ω C D E:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable [NormedAddCommGroup D][NormedSpace ℝ D][MeasurableSpace D][BorelSpace D][SecondCountableTopology D]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

/-- Actual predictable L2 column actions commute with deterministic
past-event restriction. -/
theorem event_map(L:C→L[ℝ]D)(v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A)
    (f:Process (E:=C) 𝓕 μ H):
    (L.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕)))
      (eventProcess 𝓕 μ H v A hA f)=
      eventProcess 𝓕 μ H v A hA
        ((L.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) f):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [ae_eq_of_ae_eq_trim (L.coeFn_compLpL (eventProcess 𝓕 μ H v A hA f)),
    ae_eq_of_ae_eq_trim (L.coeFn_compLpL f),eventProcess_ae 𝓕 μ H v A hA f,
    eventProcess_ae 𝓕 μ H v A hA
      ((L.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) f)] with p hp hf he ho
  rw [hp,he,ho]
  by_cases ha:p∈eventAfter v A
  · rw [Set.indicator_of_mem ha,Set.indicator_of_mem ha,hf]
  · rw [Set.indicator_of_notMem ha,Set.indicator_of_notMem ha,map_zero]

theorem post_map(L:C→L[ℝ]D)(v:ℝ≥0)(f:Process (E:=C) 𝓕 μ H):
    (L.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) (post 𝓕 μ H v f)=
      post 𝓕 μ H v ((L.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) f):=
  event_map 𝓕 μ H L v univ MeasurableSet.univ f

section Rotation
variable [NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(Φ:ℝ≥0×Ω→D→ₗᵢ[ℝ]C)
variable(hΦ:@Measurable ((ℝ≥0×Ω)×D) C (𝓕.predictable.prod ‹MeasurableSpace D›) ‹MeasurableSpace C›
  (fun p=>Φ p.1 p.2))

theorem event_isometry(v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A)(f:Process (E:=D) 𝓕 μ H):
    processIsometry 𝓕 μ H Φ hΦ (eventProcess 𝓕 μ H v A hA f)=
      eventProcess 𝓕 μ H v A hA (processIsometry 𝓕 μ H Φ hΦ f):=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [processIsometry_ae 𝓕 μ H Φ hΦ (eventProcess 𝓕 μ H v A hA f),
    processIsometry_ae 𝓕 μ H Φ hΦ f,eventProcess_ae 𝓕 μ H v A hA f,
    eventProcess_ae 𝓕 μ H v A hA (processIsometry 𝓕 μ H Φ hΦ f)] with p hp hf he ho
  rw [hp,he,ho]
  by_cases ha:p∈eventAfter v A
  · rw [Set.indicator_of_mem ha,Set.indicator_of_mem ha,hf]
  · rw [Set.indicator_of_notMem ha,Set.indicator_of_notMem ha,map_zero]

/-- Ordinary past locality survives a genuine predictable Hilbert
isometry of the original noise coordinates. -/
theorem rotation(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J):
    StandardTerminalPastLocality (PredictableItoRotation.integral 𝓕 μ H Φ hΦ J):=by
  intro v A hA f
  have he:=hlocal v A hA (processIsometry 𝓕 μ H Φ hΦ f)
  rw [←event_isometry 𝓕 μ H Φ hΦ v A hA f,
    PastItoAlgebra.post_isometry 𝓕 μ H Φ hΦ v f] at he
  exact he
end Rotation
end SHE.ItoLocalityTransport

namespace SHE.NativeHilbertPastLocality
open Set MeasureTheory PredictableL2 PastItoInputs NativeObservationNaturality FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (OrthogonalItoChannels.Both RealHaarInput):=borel _
local instance : BorelSpace (OrthogonalItoChannels.Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)

/-- Scalar locality and the SAME-noise scalar/Hilbert naturality give
actual Hilbert past locality by a countable separating dual family. -/
theorem of_naturality
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:StandardScalarNaturality I J)(hlocal:StandardTerminalPastLocality J):
    StandardTerminalPastLocality I:=by
  intro v A hA f
  have hz:(fun ω=>I.integral (eventProcess 𝓕 μ H v A hA f) ω-
      A.indicator (I.integral (post 𝓕 μ H v f)) ω)=ᵐ[μ] (0:Ω→RealL2):=by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    let T:RealHaarIntegrand.Columns→L[ℝ]RealHaarInput:=HilbertColumns.mapCLM L
    have hc0:=L.coeFn_compLpL (I.integral (eventProcess 𝓕 μ H v A hA f))
    have hc1:=L.coeFn_compLpL (I.integral (post 𝓕 μ H v f))
    rw [hIJ.commutes] at hc0 hc1
    have he:=hlocal v A hA ((T.compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) f)
    rw [←ItoLocalityTransport.event_map 𝓕 μ H T v A hA f,
      ←ItoLocalityTransport.post_map 𝓕 μ H T v f] at he
    filter_upwards [hc0,hc1,he] with ω hc0 hc1 he
    change L (_-_)=0
    by_cases hω:ω∈A
    · rw [Set.indicator_of_mem hω,map_sub]
      rw [Set.indicator_of_mem hω] at he
      exact sub_eq_zero.mpr (hc0.symm.trans (he.trans hc1))
    · rw [Set.indicator_of_notMem hω,map_sub,map_zero,sub_zero]
      rw [Set.indicator_of_notMem hω] at he
      exact hc0.symm.trans he
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

theorem left
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (K:StandardTerminalIto (C:=OrthogonalItoChannels.Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hI:StandardScalarNaturality I (OrthogonalItoChannels.leftIntegral 𝓕 μ H K))
    (hlocal:StandardTerminalPastLocality K):StandardTerminalPastLocality I:=by
  apply of_naturality 𝓕 μ H I (OrthogonalItoChannels.leftIntegral 𝓕 μ H K) hI
  exact ItoLocalityTransport.rotation 𝓕 μ H
    (fun _=>OrthogonalItoChannels.left (C:=RealHaarInput))
    (OrthogonalItoChannels.left_measurable 𝓕) K hlocal

theorem right
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (K:StandardTerminalIto (C:=OrthogonalItoChannels.Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hI:StandardScalarNaturality I (OrthogonalItoChannels.rightIntegral 𝓕 μ H K))
    (hlocal:StandardTerminalPastLocality K):StandardTerminalPastLocality I:=by
  apply of_naturality 𝓕 μ H I (OrthogonalItoChannels.rightIntegral 𝓕 μ H K) hI
  exact ItoLocalityTransport.rotation 𝓕 μ H
    (fun _=>OrthogonalItoChannels.right (C:=RealHaarInput))
    (OrthogonalItoChannels.right_measurable 𝓕) K hlocal
end SHE.NativeHilbertPastLocality
