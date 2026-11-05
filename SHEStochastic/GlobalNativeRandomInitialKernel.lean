module

public import SHEStochastic.GlobalNativePositiveWeakExistence
public import SHE.AdditivePhysicalFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.GlobalNativeRandomInitialKernel
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open PositiveScalarApproximation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

def restrict (P : FiniteScalarIto.Family F μ H ι) (K : ℝ≥0) (hK : K ≤ H) :
    FiniteScalarIto.Family F μ K ι where
  W := P.W
  adapted := P.adapted
  continuous := P.continuous
  law n j := ⟨fun t ht ↦ (P.law n j).1 t (fun i ↦ (ht i).trans hK),
    fun s t hst ht ↦ (P.law n j).2 s t hst (ht.trans hK)⟩

theorem rate_one_le : 1 ≤ NativeClock.rate := by
  change (1 : ℝ) ≤ (2*Real.pi)^2
  nlinarith [Real.pi_gt_three]

/-- Build an initial-law-specific native continuation kernel from any
source Brownian family. The spatial bases and the physical heat clock
are chosen internally; the initial law needs only its L2 moment. -/
theorem exists_kernel (P : FiniteScalarIto.Family F μ H ι)
    (q : HilbertBasis ι ℝ (Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))))
    {a : ℝ → ℝ} {C β : ℝ≥0} (ha : HolderWith C β a) (hβ : 0 < β) (hβ1 : β < 1)
    (ell cap : ℝ) (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hH : 0 < H)
    (ρ : Measure RealL2) [IsProbabilityMeasure ρ] (hρ : MemLp (id : RealL2 → RealL2) 2 ρ) :
    ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) H),
      CanonicalInitialKernel.initialLaw H Q.toMeasure = ρ ∧
      GlobalNativeFourierLimitKernel.Supports H hH Q.toMeasure (root_holder ha hβ ell cap hell hb)
        hβ hβ1 (bound cap) (root_bound ell cap hb) q := by
  let T := H/NativeClock.rate
  have hT : T ≤ H := div_le_self (by positivity) rate_one_le
  have hTp : 0 < T := div_pos hH NativeClock.rate_pos
  let b := HilbertBasis.ofRepr (NativePhysicalState.equivalence.trans q.repr)
  let U := NativePhysicalState.equivalence.symm.trans (AdditivePhysicalFactor.whiteCoordinates 1 zero_lt_one).symm
  let e := HilbertBasis.ofRepr (U.symm.trans q.repr)
  let Pc := RandomInitialBrownianFamily.family ρ μ F T (restrict F μ H P T hT)
  let Fc := RandomInitialBrownianFamily.filtration ρ μ F
  let ν := IndependentNoiseCompletion.measure ρ μ
  have hZ : MemLp (Prod.fst : RandomInitialBrownianFamily.Space ρ μ → RealL2) 2 ν :=
    hρ.comp_measurePreserving (IndependentNoiseCompletion.fst_preserving ρ μ)
  have hex : ∀ hKpos : 0<GlobalNativePositiveWeakExistence.horizon T, ∃ Q : ProbabilityMeasure (CanonicalFourierFluctuation.Space (ι := ι) (GlobalNativePositiveWeakExistence.horizon T)),
      CanonicalInitialKernel.initialLaw (GlobalNativePositiveWeakExistence.horizon T) Q.toMeasure = ρ ∧
      GlobalNativeFourierLimitKernel.Supports (GlobalNativePositiveWeakExistence.horizon T)
        hKpos Q.toMeasure
        (root_holder ha hβ ell cap hell hb) hβ hβ1 (bound cap) (root_bound ell cap hb) q := by
    intro hKpos
    obtain ⟨Q, hi, hs⟩ := GlobalNativePositiveWeakExistence.exists_kernel Fc ν T Pc e b q ha hβ hβ1 ell cap hell hb
      hTp (RandomInitialBrownianFamily.contains_null ρ μ F) Prod.fst
      (RandomInitialBrownianFamily.initial_adapted ρ μ F 0).stronglyMeasurable hZ
    refine ⟨Q, ?_, hs⟩
    exact (CanonicalInitialKernel.initialLaw_eq_of_joint _ Q.toMeasure ν Prod.fst
      (IndependentNoiseCompletion.fst_preserving ρ μ).measurable hi).trans
        (IndependentNoiseCompletion.fst_preserving ρ μ).map_eq
  have hK : GlobalNativePositiveWeakExistence.horizon T = H := by
    change NativeClock.rate*(H/NativeClock.rate)=H
    field_simp [NativeClock.rate_pos.ne']
  rw [hK] at hex
  exact hex hH

end SHEStochastic.GlobalNativeRandomInitialKernel
