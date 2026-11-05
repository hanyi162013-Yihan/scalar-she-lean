module
public import SHE.ConditionalPathLawStitching
public import SHE.CanonicalContinuousStateDriver
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.ConditionalInitialState
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory
variable {Ω P F E : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace F]
variable [StandardBorelSpace F] [Nonempty F]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

/-- A state determined by the observed prefix is fixed, with its actual
value, under almost every genuine conditional future law. -/
theorem known_state (X : Ω→P) (Y : Ω→F) (hX : Measurable X) (hY : Measurable Y)
    (state : F→E) (known : P→E) (hs : Measurable state) (hk : Measurable known)
    (he : (fun ω=>state (Y ω))=ᵐ[μ] fun ω=>known (X ω)) :
    ∀ᵐp∂μ.map X,∀ᵐy∂condDistrib Y X μ p,state y=known p := by
  apply Measure.ae_ae_of_ae_compProd (μ:=μ.map X) (κ:=condDistrib Y X μ)
    (p:=fun z:P×F=>state z.2=known z.1)
  rw [compProd_map_condDistrib hX.aemeasurable hY.aemeasurable]
  exact (ae_map_iff (hX.prodMk hY).aemeasurable
    (measurableSet_eq_fun (hs.comp measurable_snd) (hk.comp measurable_fst))).mpr he

variable [CompleteSpace E]

/-- In particular the restarted continuous state path starts at the
actual terminal state of its prefix, without a new initial-law premise. -/
theorem continuous_initial (H : ℝ≥0) (X : Ω→P)
    (Y : Ω→C(Icc (0:ℝ) (H:ℝ),E)) (hX : Measurable X) (hY : Measurable Y)
    (known : P→E) (hk : Measurable known)
    (he : (fun ω=>Y ω ⟨0,le_rfl,H.2⟩)=ᵐ[μ] fun ω=>known (X ω)) :
    ∀ᵐp∂μ.map X,∀ᵐy∂condDistrib Y X μ p,y ⟨0,le_rfl,H.2⟩=known p :=
  known_state μ X Y hX hY (fun y=>y ⟨0,le_rfl,H.2⟩) known
    (ContinuousMap.measurable_eval _) hk he
end SHE.ConditionalInitialState
