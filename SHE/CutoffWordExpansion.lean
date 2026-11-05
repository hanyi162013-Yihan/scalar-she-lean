module

public import SHE.CutoffWordStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Finite stochastic word expansion for the genuine recursive cutoff
words. Only the ordinary finite-dimensional Itô formula and centering
remain stochastic inputs. All finite-level analytic and Borel conditions
are discharged by the actual Gaussian/insertion word construction. -/
noncomputable section
universe u v
namespace SHE.CutoffWordExpansion
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion GaussianItoTest CutoffWordLevel CutoffWordHistories CutoffWordAnalytic CutoffWordStep
open IntegratedPhysicalStep

structure System (R : ReferenceData) (P : Type u) (Ω : Type v) [MeasurableSpace P]
    (n : ℕ) where
  initial : Level R P n
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  state : Ω × ℝ → CircleL2
  field : Ω × (ℝ × HeatCircle) → ℝ
  stochasticTerm : (k : ℕ) → History P k → (ℝ → WordRecursion.State (n+k) → ℝ) → Ω → ℝ

namespace System
variable {R : ReferenceData} {P : Type u} {Ω : Type v} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n : ℕ} (S : System R P Ω n)

def level (k : ℕ) : Level R (History P k) (n+k) := iterate S.initial S.cutoff S.cutoff_pos k

def data (k : ℕ) : LevelData (History P k) Ω (n+k) :=
  physicalLevel (S.level k) S.state S.field (S.stochasticTerm k)

def leafMass (μ : Measure P) (k : ℕ) (ω : Ω) : ℝ :=
  ∫ p, (S.data k).leaf p ω ∂historyMeasure R μ k

def referenceMass (μ : Measure P) (k : ℕ) (ω : Ω) : ℝ :=
  ∫ p, (S.data k).reference p ω ∂historyMeasure R μ k

def noiseMass (μ : Measure P) (k : ℕ) : Ω → ℝ :=
  (S.data k).integratedNoise (historyMeasure R μ k)

def correctionMass (μ : Measure P) (k : ℕ) (ω : Ω) : ℝ :=
  ∫ p, cutoffCorrection (S.level k) S.cutoff S.state S.field p ω ∂historyMeasure R μ k

theorem recursive_step (hU : Measurable S.state) (hX : Measurable S.field)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (k : ℕ) (hIto : ItoConditions (S.data k) τ) :
    Integrable (S.noiseMass μ k) τ ∧ (∫ ω, S.noiseMass μ k ω ∂τ) = 0 ∧
      ∀ ω, S.leafMass μ k ω = S.referenceMass μ k ω + S.noiseMass μ k ω +
        S.leafMass μ (k+1) ω + S.correctionMass μ k ω := by
  exact integrated_recursive_step (S.level k) S.cutoff S.cutoff_pos S.state S.field hU hX
    (S.stochasticTerm k) (historyMeasure R μ k) τ hIto

/-- An exact finite physical expansion. The last leaf and every cutoff
correction remain visible, so this theorem contains no hidden infinite
series or boundary-removal assertion. -/
theorem finite_expansion (hU : Measurable S.state) (hX : Measurable S.field)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (depth : ℕ) (hIto : ∀ k < depth, ItoConditions (S.data k) τ) :
    Integrable (fun ω => ∑ k ∈ Finset.range depth, S.noiseMass μ k ω) τ ∧
      (∫ ω, ∑ k ∈ Finset.range depth, S.noiseMass μ k ω ∂τ) = 0 ∧
      ∀ ω, S.leafMass μ 0 ω =
        (∑ k ∈ Finset.range depth, S.referenceMass μ k ω) +
        (∑ k ∈ Finset.range depth, S.noiseMass μ k ω) +
        (∑ k ∈ Finset.range depth, S.correctionMass μ k ω) + S.leafMass μ depth ω := by
  have hstep (k : ℕ) (hk : k < depth) := S.recursive_step hU hX μ τ k (hIto k hk)
  have hNi : ∀ k ∈ Finset.range depth, Integrable (S.noiseMass μ k) τ :=
    fun k hk => (hstep k (Finset.mem_range.mp hk)).1
  refine ⟨integrable_finsetSum _ hNi, ?_, fun ω => ?_⟩
  · rw [integral_finsetSum _ hNi]
    apply Finset.sum_eq_zero
    intro k hk
    exact (hstep k (Finset.mem_range.mp hk)).2.1
  · have htel : ∀ m ≤ depth, S.leafMass μ 0 ω =
        (∑ k ∈ Finset.range m, S.referenceMass μ k ω) +
        (∑ k ∈ Finset.range m, S.noiseMass μ k ω) +
        (∑ k ∈ Finset.range m, S.correctionMass μ k ω) + S.leafMass μ m ω := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have he := ih (Nat.le_trans (Nat.le_succ m) hm)
        have hs := (hstep m (Nat.lt_of_succ_le hm)).2.2 ω
        simp only [Finset.sum_range_succ]
        linarith only [he,hs]
    exact htel depth le_rfl

end System
end SHE.CutoffWordExpansion
