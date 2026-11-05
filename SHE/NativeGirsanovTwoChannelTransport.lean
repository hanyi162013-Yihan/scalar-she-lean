module
public import SHE.NativeGirsanovHilbertLift
public import SHE.TwoChannelItoRows
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
/-- The selected ordinary integral-transport identity from package7. -/
structure GirsanovIntegralTransport {Ω C:Type*}[MeasurableSpace Ω]
    [NormedAddCommGroup C][InnerProductSpace ℝ C]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ Q:Measure Ω)(H:ℝ≥0)
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H)
    (u:Process (E:=C) 𝓕 μ H):Prop where
  transport : ∀(f:Process (E:=C) 𝓕 μ H)(g:Process (E:=C) 𝓕 Q H),
    (∀ᵐp∂energyMeasure μ H,f p=g p)→
      (∀ᵐω∂Q,K.integral g ω=J.integral f ω+
        ∫s,inner ℝ (f (s,ω)) (u (s,ω)) ∂timeMeasure H)
end SHE
namespace SHE.NativeGirsanovTwoChannelTransport
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

def block(L:RealL2→L[ℝ]ℝ)(v w:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    Process (E:=Both RealHaarInput) 𝓕 μ H:=
  TwoChannelItoRows.block 𝓕 μ H
    (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) v)
    (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) w)

theorem block_ae(L:RealL2→L[ℝ]ℝ)(v w:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    block 𝓕 μ H L v w=ᵐ[energyMeasure μ H]
      (fun p=>WithLp.toLp 2 (HilbertColumns.mapCLM L (v p),HilbertColumns.mapCLM L (w p))):=by
  filter_upwards [TwoChannelItoRows.block_ae 𝓕 μ H
    (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) v)
    (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) w),
    ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLpL v),
    ae_eq_of_ae_eq_trim ((HilbertColumns.mapCLM L).coeFn_compLpL w)] with p hp hv hw
  unfold block
  rw [hp,hv,hw]

variable [IsProbabilityMeasure μ]
theorem observed_integral
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (hI0:StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
    (hI1:StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J))
    (L:RealL2→L[ℝ]ℝ)(v w:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H):
    (fun ω=>L (I0.integral v ω)+L (I1.integral w ω))=ᵐ[μ]
      J.integral (block 𝓕 μ H L v w):=by
  have h0:=L.coeFn_compLpL (I0.integral v)
  have h1:=L.coeFn_compLpL (I1.integral w)
  rw [hI0.commutes L v] at h0
  rw [hI1.commutes L w] at h1
  have hb:=Lp.coeFn_add
    ((leftIntegral 𝓕 μ H J).integral
      (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) v))
    ((rightIntegral 𝓕 μ H J).integral
      (((HilbertColumns.mapCLM L).compLpL 2 ((energyMeasure μ H).trim (predictable_le_product 𝓕))) w))
  rw [←TwoChannelItoRows.integral_block] at hb
  filter_upwards [h0,h1,hb] with ω h0 h1 hb
  rw [←h0,←h1]
  exact hb.symm

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
      (A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 Q H),
      StandardScalarNaturality A0 (leftIntegral 𝓕 Q H K) ∧
      StandardScalarNaturality A1 (rightIntegral 𝓕 Q H K) ∧
      ∀(L:RealL2→L[ℝ]ℝ)
        (v w:Process (E:=RealHaarIntegrand.Columns) 𝓕 μ H)
        (v' w':Process (E:=RealHaarIntegrand.Columns) 𝓕 Q H),
        (∀ᵐp∂energyMeasure μ H,v p=v' p)→
        (∀ᵐp∂energyMeasure μ H,w p=w' p)→
        (fun ω=>L (A0.integral v' ω)+L (A1.integral w' ω))=ᵐ[Q]
          (fun ω=>L (I0.integral v ω)+L (I1.integral w ω)+
            ∫s,inner ℝ (block 𝓕 μ H L v w (s,ω)) (u (s,ω)) ∂timeMeasure H):=by
  dsimp only
  intro hprob hμQ hQμ
  let Q:=ExponentialChangeMeasure.measure μ (fun ω=>J.integral u ω)
    (StochasticExponential.bracket 𝓕 μ H u)
  obtain ⟨K,ht⟩:=hG.transport u hcap
  obtain ⟨A0,A1,h0,h1⟩:=NativeGirsanovHilbertLift.exists_natural 𝓕 Q H K
    (hG.hilbertTransport u hcap K)
  refine ⟨K,A0,A1,h0,h1,?_⟩
  intro L v w v' w' hv hw
  have hprod:energyMeasure μ H≪energyMeasure Q H:=
    (Measure.AbsolutelyContinuous.refl (timeMeasure H)).prod hμQ
  have hb:∀ᵐp∂energyMeasure μ H,block 𝓕 μ H L v w p=block 𝓕 Q H L v' w' p:=by
    filter_upwards [block_ae 𝓕 μ H L v w,hprod.ae_le (block_ae 𝓕 Q H L v' w'),hv,hw] with p hp hq hv hw
    rw [hp,hq,hv,hw]
  filter_upwards [observed_integral 𝓕 Q H K A0 A1 h0 h1 L v' w',
    hQμ.ae_le (observed_integral 𝓕 μ H J I0 I1 hI0 hI1 L v w),
    ht (block 𝓕 μ H L v w) (block 𝓕 Q H L v' w') hb] with ω hnew hold htr
  rw [hnew,htr,hold]
end SHE.NativeGirsanovTwoChannelTransport
