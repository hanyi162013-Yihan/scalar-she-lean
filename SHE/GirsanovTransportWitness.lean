module
public import SHE.NativeGirsanovTwoChannelTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
/-- The selected control and the literal ordinary change-of-integral
identity. This bundles existing Girsanov data; it is no additional input. -/
structure GirsanovTransportWitness {Ω C:Type*}[MeasurableSpace Ω]
    [NormedAddCommGroup C][InnerProductSpace ℝ C]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ Q:Measure Ω)(H:ℝ≥0)
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H) where
  control:Process (E:=C) 𝓕 μ H
  transport:∀(f:Process (E:=C) 𝓕 μ H)(g:Process (E:=C) 𝓕 Q H),
    (∀ᵐ(p:ℝ≥0×Ω)∂energyMeasure μ H,f p=g p)→
    (∀ᵐ(ω:Ω)∂Q,K.integral g ω=J.integral f ω+
      ∫s,inner ℝ (f (s,ω)) (control (s,ω)) ∂timeMeasure H)
end SHE
