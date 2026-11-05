module
public import SHE.StandardTerminalLevy
public import SHE.RotatedItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.PredictableItoRotation
open MeasureTheory PredictableL2 StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω A C:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup A][InnerProductSpace ℝ A][MeasurableSpace A][BorelSpace A]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω) (H:ℝ≥0)
variable (Φ:(ℝ≥0×Ω)→A→ₗᵢ[ℝ]C)
variable (hΦ:@Measurable ((ℝ≥0×Ω)×A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p=>Φ p.1 p.2))

/-- Brownian recognition is preserved by the ACTUAL predictable
isometry. Once ordinary Levy is accepted, no separate rotation-law
axiom is needed for these full Hilbert-coordinate stochastic inputs. -/
theorem levy (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (hLevy:StandardTerminalLevy J):StandardTerminalLevy (integral 𝓕 μ H Φ hΦ J):=by
  intro n R X G hpred hcont hversion hgram
  apply hLevy n (fun i=>processIsometry 𝓕 μ H Φ hΦ (R i)) X G hpred hcont
  · intro t ht
    filter_upwards [hversion t ht] with ω hω i
    have he: (integral 𝓕 μ H Φ hΦ J).integral (stop 𝓕 μ H t (R i))=
        J.integral (stop 𝓕 μ H t (processIsometry 𝓕 μ H Φ hΦ (R i))):=by
      change J.integral (processIsometry 𝓕 μ H Φ hΦ (stop 𝓕 μ H t (R i)))=_
      rw [RotatedItoAlgebra.map_stop]
    rw [←he]
    exact hω i
  · have hall:∀ᵐp∂energyMeasure μ H,∀i:Fin n,
        processIsometry 𝓕 μ H Φ hΦ (R i) p=Φ p (R i p):=
      ae_all_iff.mpr (fun i=>processIsometry_ae 𝓕 μ H Φ hΦ (R i))
    filter_upwards [hall,hgram] with p hp hg i j
    rw [hp i,hp j,(Φ p).inner_map_map]
    exact hg i j
end SHE.PredictableItoRotation
