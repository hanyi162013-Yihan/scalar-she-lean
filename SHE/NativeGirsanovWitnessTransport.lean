module
public import SHE.GirsanovTransportWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeGirsanovWitnessTransport
open MeasureTheory PredictableL2 FiniteHaar DyadicApproximation OrthogonalItoChannels NativeObservationNaturality
open scoped NNReal ENNReal
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

variable [IsProbabilityMeasure μ]
/-- Ordinary package7 supplies natural Hilbert maps for the SAME changed
scalar integral, and transports both observed channels together. -/
theorem exists_transport
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hG:StandardTerminalGirsanov J)
    (u:Process (E:=Both RealHaarInput) 𝓕 μ H)
    (hcap:∀ᵐω∂μ,StochasticExponential.bracket 𝓕 μ H u ω≤1)
    (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (hI0:StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
    (hI1:StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J)):
    let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
      (StochasticExponential.bracket 𝓕 μ H u)
    ∀ [IsProbabilityMeasure Q],μ≪Q→Q≪μ→
    ∃(K:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 Q H)
      (T:GirsanovTransportWitness 𝓕 μ Q H J K)
      (A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H),
      T.control=u ∧
      StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K) ∧
      StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K) ∧
      ∀(L:RealL2→L[ℝ]ℝ)
        (v w:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H)
        (v' w':Process (E:=RealHaarIntegrand.Columns) 𝓕 Q H),
        (∀ᵐp∂energyMeasure μ H,v p=v' p)→
        (∀ᵐp∂energyMeasure μ H,w p=w' p)→
        (fun ω=>L (A0.integral v' ω)+L (A1.integral w' ω))=ᵐ[Q]
          (fun ω=>L (I0.integral v ω)+L (I1.integral w ω)+
            ∫s,inner ℝ (NativeGirsanovTwoChannelTransport.block 𝓕 μ H L v w (s,ω)) (u (s,ω)) ∂timeMeasure H):=by
  dsimp only
  intro hprob hμQ hQμ
  let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  obtain ⟨K,ht⟩:=hG.transport u hcap
  obtain ⟨A0,A1,h0,h1⟩:=NativeGirsanovHilbertLift.exists_natural 𝓕 Q H K
    (hG.hilbertTransport u hcap K)
  let T:GirsanovTransportWitness 𝓕 μ Q H J K:=⟨u,ht⟩
  refine ⟨K,T,A0,A1,rfl,h0,h1,?_⟩
  intro L v w v' w' hv hw
  have hprod:energyMeasure μ H≪energyMeasure Q H:=
    (Measure.AbsolutelyContinuous.refl (timeMeasure H)).prod hμQ
  have hb:∀ᵐp∂energyMeasure μ H,NativeGirsanovTwoChannelTransport.block 𝓕 μ H L v w p=NativeGirsanovTwoChannelTransport.block 𝓕 Q H L v' w' p:=by
    filter_upwards [NativeGirsanovTwoChannelTransport.block_ae 𝓕 μ H L v w,hprod.ae_le (NativeGirsanovTwoChannelTransport.block_ae 𝓕 Q H L v' w'),hv,hw] with p hp hq hv hw
    rw [hp,hq,hv,hw]
  filter_upwards [NativeGirsanovTwoChannelTransport.observed_integral 𝓕 Q H K A0 A1 h0 h1 L v' w',
    hQμ.ae_le (NativeGirsanovTwoChannelTransport.observed_integral 𝓕 μ H J I0 I1 hI0 hI1 L v w),
    ht (NativeGirsanovTwoChannelTransport.block 𝓕 μ H L v w) (NativeGirsanovTwoChannelTransport.block 𝓕 Q H L v' w') hb] with ω hnew hold htr
  rw [hnew,htr,hold]
end SHE.NativeGirsanovWitnessTransport
