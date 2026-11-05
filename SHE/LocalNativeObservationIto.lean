module

public import SHE.LocalNativeItoBracket
public import SHE.NativeObservationIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual finite physical Itô observations on arbitrary local cutoff
windows. Their targets may lie inside the global noise horizon. The
proved stopped-path construction discharges the same universal ordinary
Itô input, without adding a local-window stochastic black box. -/
noncomputable section
namespace SHE.LocalNativeObservationIto
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality WordRecursion
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
local instance localNativeObservationIto_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance localNativeObservationIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance localNativeObservationIto_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n → Observation) (b : ℝ≥0)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(b:ℝ))

include hδ hgap in
theorem stoppedValue_eq_observe (U : ℝ≥0 × Ω → RealL2) (X : Ω → ℝ × HeatCircle → ℝ)
    (ω : Ω) {t : ℝ} (ht0 : 0 ≤ t) (htb : t ≤ (b:ℝ)) :
    LocalNativeObservations.stoppedValue δ Z U b (t.toNNReal,ω)=
      observe (fun r => embed (U (r.toNNReal,ω))) (X ω) Z t := by
  have htn : t.toNNReal ≤ b := (Real.toNNReal_le_iff_le_coe).mpr htb
  rw [LocalNativeObservations.stoppedValue,min_eq_left htn]
  exact NativeObservationIto.value_eq_observe b Z hδ hgap U X ω ht0 htb

include hM hf hδ hgap in
/-- Genuine local-window physical Itô input, with the actual centered
gradient-row scalar integral. The only model premise is the literal
native mild identity and its actual kernel input representation. -/
theorem finiteItoInput
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J) (hJ : StandardFiniteIto.Universal 𝓕 μ h J)
    (u : RealL2) (U : ℝ≥0 × Ω → RealL2) (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (v : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : ∀ t : ℝ≥0,t ≤ h → v t =ᵐ[energyMeasure μ h]
      (fun p => kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)))
    (hmild : ∀ (t : ℝ≥0),t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=heat t u+I.integral (v t) ω)
    (hb : b ≤ h) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ (b:ℝ))
    (X : Ω → ℝ × HeatCircle → ℝ) :
    ∃ N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω => observe (fun r => embed (U (r.toNNReal,ω))) (X ω) Z)
        (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b N := by
  let Y := LocalNativeObservations.stoppedValue δ Z U b
  let R := LocalNativeObservations.rows 𝓕 μ h hell hM f hf Z b hδ hgap
  have hRep := LocalNativeObservations.integral_representation 𝓕 μ h hell hM f hf Z b hδ hgap
    I J hIJ u U v hv hmild hb
  have hY := LocalNativeObservations.predictable_of_representation 𝓕 μ h hell hM f hf Z b hδ hgap
    hnull J (PositiveGapObservations.initial Z u) U hc hRep
  let N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ := fun G ω =>
    FiniteItoNoise.noise 𝓕 μ h Y hY R J a b G ω
  have hi := StandardFiniteIto.finiteItoInput 𝓕 μ h J hJ R (PositiveGapObservations.initial Z u) Y hY
    (fun ω => LocalNativeObservations.stoppedValue_continuous δ Z U b (hc ω))
    (fun t _ => hRep t) ha hab (by exact_mod_cast hb)
  have hd := LocalNativeItoBracket.finiteItoInput_of_density 𝓕 μ h hell hM f hf Z b hδ hgap hb ha hab _ N hi
  have hp := NativeObservationIto.finiteItoInput_congr_path μ hab hd
    (fun ω t ht => stoppedValue_eq_observe (Z := Z) (b := b) (hδ := hδ) (hgap := hgap)
      U X ω (ha.trans ht.1) ht.2)
  refine ⟨N,fun G => ⟨?_,?_⟩,hp⟩
  · exact FiniteItoNoise.noise_integrable 𝓕 μ h Y hY R J a b G
  · exact FiniteItoNoise.noise_centered 𝓕 μ h Y hY R J a b G

end SHE.LocalNativeObservationIto
