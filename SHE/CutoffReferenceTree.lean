module

public import SHE.CutoffWordExpansion
public import SHE.CanonicalConditional

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Deterministic Gaussian reference trees selected by a true initial
physical L² state. Inactive cutoff histories carry the zero test, so
no point evaluation of an arbitrary L² representative is introduced at
age zero. The original observation stops remain unchanged. -/
noncomputable section
namespace SHE.CutoffReferenceTree
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion GaussianItoTest CutoffWordLevel CutoffWordHistories CutoffWordAnalytic CutoffWordStep
open IntegratedPhysicalStep CanonicalConditional CutoffWordExpansion
open Classical
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ}

def RegularAtBase (L : Level R P n) : Prop :=
  ∀ p, (∀ i, R.base < (L.observations.observations p i).target) ∨ L.test p = 0

theorem extend_regularAtBase (L : Level R P n) (δ : ℝ) (hδ : 0 < δ) :
    RegularAtBase (L.extend δ hδ) := by
  intro p
  by_cases hp : L.Good δ p
  · left
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change R.base < L.nodeTime p
      rw [L.nodeTime_eq hδ hp]
      exact hp.1
    · change R.base < (L.observations.observations p.1 j).target
      exact (L.good_time hδ hp).1.trans ((L.good_time hδ hp).2.trans_le (L.targets_after p.1 j))
  · right
    change L.childTest δ p = 0
    rw [L.childTest_eq hδ p,ite_eq_right hp]

theorem iterate_regularAtBase (L : Level R P n) (δ : ℝ) (hδ : 0 < δ)
    (hL : RegularAtBase L) (k : ℕ) : RegularAtBase (iterate L δ hδ k) := by
  cases k with
  | zero => exact hL
  | succ k => exact extend_regularAtBase _ δ hδ

def deterministicReference (L : Level R P n) (u : CircleL2) (p : P) : ℝ :=
  backward (L.window p) (L.test p) R.base
    (initialMean (L.observations.observations p) R.base u)

theorem physical_reference_eq (L : Level R P n) (hL : RegularAtBase L)
    (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)
    (N : P → (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (u : CircleL2) (ω : Ω) (hu : U (ω,R.base) = u) (p : P) :
    (physicalLevel L U X N).reference p ω = deterministicReference L u p := by
  rcases hL p with hpos | hzero
  · change backward (L.window p) (L.test p) R.base
      (observe (fun t => U (ω,t)) (fun q => X (ω,q)) (L.observations.observations p) R.base) = _
    rw [observe_initial_eq (L.observations.observations p) R.base
      (fun t => U (ω,t)) (fun q => X (ω,q)) u hu hpos]
    rfl
  · change backward (L.window p) (L.test p) R.base _ = backward _ (L.test p) R.base _
    rw [hzero]
    simp only [backward,GaussianConvolution.gaussianAverage,Pi.zero_apply,integral_zero]

theorem deterministicReference_measurable (L : Level R P n) (u : CircleL2) :
    Measurable (deterministicReference L u) := by
  change Measurable (fun p : P => backward (L.window p) (L.test p) R.base
    (initialMean (L.observations.observations p) R.base u))
  have hm : Measurable (fun p => initialMean (L.observations.observations p) R.base u) := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
    apply Measurable.of_eval
    intro i
    exact PhysicalProfile.physicalHeatMean_joint_measurable.comp
      (measurable_const.prodMk (((L.observations.target_measurable i).sub_const R.base).prodMk
        (L.observations.center_measurable i)))
  have hmap : Measurable (fun p => ((p,R.base),initialMean (L.observations.observations p) R.base u)) :=
    (measurable_id.prodMk measurable_const).prodMk hm
  have hb := (backward_measurable L).comp hmap
  simpa only [Function.comp_def] using hb

namespace System
variable (S : CutoffWordExpansion.System R P Ω n)

def referenceTree (μ : Measure P) (u : CircleL2) (k : ℕ) : ℝ :=
  ∫ p, deterministicReference (S.level k) u p ∂historyMeasure R μ k

theorem referenceMass_eq (hS : RegularAtBase S.initial) (μ : Measure P) (u : CircleL2)
    (ω : Ω) (hu : S.state (ω,R.base) = u) (k : ℕ) :
    S.referenceMass μ k ω = referenceTree S μ u k := by
  apply integral_congr_ae
  filter_upwards with p
  exact physical_reference_eq (S.level k) (iterate_regularAtBase S.initial S.cutoff S.cutoff_pos hS k)
    S.state S.field (S.stochasticTerm k) u ω hu p

/-- On the single event where the initial physical L² state is u,
every history and every depth uses the same deterministic Gaussian
reference tree. No uncountable intersection of almost-sure events occurs. -/
theorem finite_reference_expansion (hS : RegularAtBase S.initial)
    (hU : Measurable S.state) (hX : Measurable S.field)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (depth : ℕ) (hIto : ∀ k < depth, ItoConditions (S.data k) τ)
    (u : CircleL2) (hu : ∀ᵐ ω ∂τ, S.state (ω,R.base) = u) :
    Integrable (fun ω => ∑ k ∈ Finset.range depth, S.noiseMass μ k ω) τ ∧
      (∫ ω, ∑ k ∈ Finset.range depth, S.noiseMass μ k ω ∂τ) = 0 ∧
      ∀ᵐ ω ∂τ, S.leafMass μ 0 ω =
        (∑ k ∈ Finset.range depth, referenceTree S μ u k) +
        (∑ k ∈ Finset.range depth, S.noiseMass μ k ω) +
        (∑ k ∈ Finset.range depth, S.correctionMass μ k ω) + S.leafMass μ depth ω := by
  obtain ⟨hNi,hNz,he⟩ := S.finite_expansion hU hX μ τ depth hIto
  refine ⟨hNi,hNz,?_⟩
  filter_upwards [hu] with ω hω
  rw [he ω]
  congr 3
  apply Finset.sum_congr rfl
  intro k _
  exact referenceMass_eq S hS μ u ω hω k

end System
end SHE.CutoffReferenceTree
