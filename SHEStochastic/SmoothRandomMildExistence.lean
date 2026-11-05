module

public import SHE.SmoothMildExistence
public import SHEStochastic.RandomHeatInitialProcess

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.SmoothRandomMildExistence
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology StateL2 := inferInstance
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (hH : (H : ℝ) ≤ 1)
  {a : ℝ → ℝ} (ha : Measurable a) {ell cap K β : ℝ}
  (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
  (hβ : 0 < β) (hK : 0 ≤ K) (hholder : ∀ z w, |a z - a w| ≤ K * |z - w| ^ β)
  (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H)
  (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B)
  (hpos : 0 < H) (hnull : NullCompleteFiltration.ContainsNullSets F μ)

include hBDG hpos hnull hβ hK hholder in
/-- The existing fixed-horizon Picard theorem gives actual continuous
smooth mild solutions for square-integrable random initial states.
This is the approximation existence needed for an exit-law-specific
continuation; a solution kernel is not a premise. -/
theorem exists_mild {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
    (Z : Ω → StateL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ U : ℝ≥0 → Ω → StateL2, (∀ sample, Continuous (fun t ↦ U t sample)) ∧
      StronglyMeasurable[F.predictable] (Function.uncurry U) ∧
      ∃ hfield : StronglyMeasurable[F.predictable]
        (ContinuousHeatMild.coefficientFunction ha hell hb U),
        ∀ (t : ℝ≥0) (ht : t ≤ H), U t =ᵐ[μ] fun sample ↦
          RealHeat.realHeat (t : ℝ) (Z sample) +
            DampedFixedIntegral.value F μ H hH (Λ := 0) (by norm_num) hell
              (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (ContinuousHeatMild.coefficientFunction ha hell hb U) hfield I t ht sample := by
  let z := RandomHeatInitialProcess.process F μ H 1 Z hZ₀ hZ
  let forcing (t : ℝ≥0) (sample : Ω) := RandomHeatInitialProcess.function 1 Z (t, sample)
  have hfc : ∀ sample, Continuous (fun t ↦ forcing t sample) :=
    RandomHeatInitialProcess.continuous_paths 1 Z
  have hfp : StronglyMeasurable[F.predictable] (Function.uncurry forcing) :=
    RandomHeatInitialProcess.predictable F 1 Z hZ₀
  have hz : z =ᵐ[energyMeasure μ H] Function.uncurry forcing :=
    RandomHeatInitialProcess.process_ae F μ H 1 Z hZ₀ hZ
  obtain ⟨v, hv, _⟩ := FixedHorizonPicard.exists_unique_forced F μ H hH (Λ := 0) (by norm_num)
    ha hell hb hβ hK hholder I B hBDG hpos hLip z
  obtain ⟨U, hc, hp, _, hfield, hmild⟩ := ContinuousDampedForced.continuous_representative
    F μ H hH (Λ := 0) (by norm_num) ha hell hb hβ hK hholder I hpos hnull B hBDG
    forcing hfc hfp z hz v hv
  refine ⟨U, hc, hp, hfield, ?_⟩
  intro t ht
  simpa only [forcing, RandomHeatInitialProcess.function, one_mul] using hmild t ht

end SHEStochastic.SmoothRandomMildExistence
