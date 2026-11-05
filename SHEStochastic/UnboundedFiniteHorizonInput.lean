module

public import SHEStochastic.SublinearHeatFiniteHorizon
public import SHEStochastic.UnboundedHeatFamily
public import SHEStochastic.NativeScalarBDGAll

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.UnboundedFiniteHorizonInput
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier AddCircle UnboundedHeatFamily
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2*Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2*Real.pi))) := ⟨rfl⟩

def energyCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*SublinearHeatFiniteHorizon.constant (T:ℝ)^(1+(β:ℝ)))*
    SublinearHeatIntegratedEnergy.stateFactor R β*
      ENNReal.ofReal ((T:ℝ)^((1-(β:ℝ))/2)/((1-(β:ℝ))/2))

theorem bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s,ω)‖^2) ∂timeMeasure H)≤
      energyCap G C β R T := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hbound
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hh := SublinearHeatFiniteHorizon.row_bound hG hβ1 T H hTH a (fun s ↦ U (s,ω)) hω
  exact (lintegral_congr fun s ↦ UnboundedHeatFamily.energy F U hU hG hβ hβ1 T a (s,ω)).trans_le hh

theorem memLp (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    @MemLp _ _ F.predictable _ _ (family F U hU hG hβ hβ1 T a) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hp := UnboundedHeatFamily.stronglyMeasurable F U hU hG hβ hβ1 T a
  have hm := hp.mono (predictable_le_product F)
  have he : (∫⁻ p, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a p‖^2) ∂energyMeasure μ H)≤energyCap G C β R T := by
    calc
      _ = ∫⁻ ω, ∫⁻ s, ENNReal.ofReal (‖family F U hU hG hβ hβ1 T a (s,ω)‖^2) ∂timeMeasure H ∂μ :=
        lintegral_prod_symm _ (hm.norm.pow 2).measurable.ennreal_ofReal.aemeasurable
      _ ≤ ∫⁻ _ : Ω, energyCap G C β R T ∂μ := lintegral_mono_ae (bracket_bound F U hU hG hβ hβ1 μ H T hTH a hbound)
      _ = _ := by simp
  have hf := he.trans_lt (show energyCap G C β R T<⊤ by
    dsimp [energyCap, SublinearHeatIntegratedEnergy.stateFactor]; finiteness)
  have hmem : MemLp (family F U hU hG hβ hβ1 T a) 2 (energyMeasure μ H) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    refine ⟨(hm.norm.pow 2).aestronglyMeasurable, ?_⟩
    change (∫⁻ p, ‖‖family F U hU hG hβ hβ1 T a p‖^2‖ₑ ∂energyMeasure μ H)<⊤
    exact (lintegral_congr fun _ ↦ Real.enorm_eq_ofReal (sq_nonneg _)).trans_lt hf
  exact (le_of_eq (eLpNorm_trim (predictable_le_product F) hp)).trans_lt hmem

/-- The original native heat integrand, now on every finite horizon.
The row is unchanged; only the proof of its finite energy is extended. -/
def input (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    Process (E := Lp V 2 (haarAddCircle (T := 2 * Real.pi))) F μ H :=
  (memLp F U hU hG hβ hβ1 μ H T hTH a hbound).toLp _

theorem input_ae (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    input F U hU hG hβ hβ1 μ H T hTH a hbound=ᵐ[energyMeasure μ H]
      family F U hU hG hβ hβ1 T a :=
  ae_eq_of_ae_eq_trim (memLp F U hU hG hβ hβ1 μ H T hTH a hbound).coeFn_toLp

theorem input_eq_local (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (hT : (T:ℝ)≤1) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    input F U hU hG hβ hβ1 μ H T hTH a hbound=
      UnboundedHeatFamily.input F U hU hG hβ hβ1 μ H T hTH hT a hbound := rfl

theorem input_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖input F U hU hG hβ hβ1 μ H T hTH a hbound (s,ω)‖^2) ∂timeMeasure H)≤energyCap G C β R T := by
  have hae := input_ae F U hU hG hβ hβ1 μ H T hTH a hbound
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hae
  filter_upwards [Measure.ae_ae_of_ae_prod hs, bracket_bound F U hU hG hβ hβ1 μ H T hTH a hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun _ hx ↦ congrArg (fun v ↦ ENNReal.ofReal (‖v‖^2)) hx)).trans_le hb

/-- Causality on the full original clock: stopping the heat row at its
observation time leaves the actual predictable input unchanged. -/
theorem input_stop (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) :
    StoppedItoInputs.stop F μ H T (input F U hU hG hβ hβ1 μ H T hTH a hbound)=
      input F U hU hG hβ hβ1 μ H T hTH a hbound := by
  apply Lp.ext
  filter_upwards [StoppedInputParameter.stop_ae_trim F μ H
    (input F U hU hG hβ hβ1 μ H T hTH a hbound) T,
    (memLp F U hU hG hβ hβ1 μ H T hTH a hbound).coeFn_toLp] with p hs hi
  rw [hs]
  by_cases ht : (p.1:ℝ)<T
  · exact Set.indicator_of_mem (show p∈StoppedItoInputs.before (Ω := Ω) T from ht) _
  · rw [Set.indicator_of_notMem (show p∉StoppedItoInputs.before (Ω := Ω) T from ht)]
    exact (hi.trans (family_zero_after F U hU hG hβ hβ1 T a p (le_of_not_gt ht))).symm

theorem input_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R) (hzero : T=0) :
    input F U hU hG hβ hβ1 μ H T hTH a hbound=0 := by
  subst T
  dsimp only [input]
  apply Lp.ext
  filter_upwards [(memLp F U hU hG hβ hβ1 μ H 0 hTH a hbound).coeFn_toLp,
    Lp.coeFn_zero (Lp V 2 (haarAddCircle (T := 2*Real.pi))) 2
      ((energyMeasure μ H).trim (predictable_le_product F))] with p hp hz
  rw [hp,hz]
  exact family_zero_after F U hU hG hβ hβ1 0 a p p.1.property

/-- Every positive integer even moment follows from the proved native
BDG theorem, also beyond the initial unit time interval. -/
theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T≤H) (a : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖≤R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (p : ℕ) (hp : 0<p) :
    (∫⁻ ω, ENNReal.ofReal (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (input F U hU hG hβ hβ1 μ H T hTH a hbound) ω‖^(2*p)) ∂μ)≤
      (NativeScalarBDGAll.constant p : ℝ≥0∞)*energyCap G C β R T^p := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2*Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  apply (NativeScalarBDGAll.power P e p hp _).trans
  calc
    _ ≤ (NativeScalarBDGAll.constant p : ℝ≥0∞)*∫⁻ _ : Ω, energyCap G C β R T^p ∂μ :=
      mul_le_mul_right (lintegral_mono_ae ((input_bracket_bound F U hU hG hβ hβ1 μ H T hTH a hbound).mono
        fun ω hω ↦ pow_le_pow_left₀ zero_le hω p)) _
    _ = _ := by simp

end SHEStochastic.UnboundedFiniteHorizonInput
