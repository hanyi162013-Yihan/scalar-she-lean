module

public import SHEStochastic.ContinuousEqualityBeforeExit
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.LocalizedFieldAssembly
open MeasureTheory Filter
open scoped NNReal

variable {Ω A E : Type*} [MeasurableSpace Ω] [TopologicalSpace A]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  (H : ℝ≥0) (τ : ℕ → Ω → WithTop ℝ≥0)
  (escape : ∀ ω, ∃ n, (H : WithTop ℝ≥0) < τ n ω)

/-- Select the first state localization that survives the whole finite
horizon. This is a countable measurable selection, not a law-selection
or weak-existence assumption. -/
def index (ω : Ω) : ℕ := by
  classical
  exact Nat.find (escape ω)

theorem index_survives (ω : Ω) : (H : WithTop ℝ≥0) < τ (index H τ escape ω) ω :=
  Nat.find_spec (escape ω)

def value (Z : ℕ → A → Ω → E) (p : A) (ω : Ω) : E := Z (index H τ escape ω) p ω

theorem measurable (Z : ℕ → A → Ω → E) (p : A)
    (hZ : ∀ n, Measurable (Z n p))
    (hτ : ∀ n, MeasurableSet {ω | (H : WithTop ℝ≥0) < τ n ω}) :
    Measurable (value H τ escape Z p) := by
  classical
  exact Measurable.find hZ hτ escape

theorem continuous (Z : ℕ → A → Ω → E)
    (hZ : ∀ n ω, Continuous (fun p ↦ Z n p ω)) (ω : Ω) :
    Continuous (fun p ↦ value H τ escape Z p ω) := hZ _ ω

/-- The assembled version agrees with each localized one before its
own exit. Only countably many cutoff levels are combined, so the
randomly selected index does not create a new null-set issue. -/
theorem agrees (μ : Measure Ω) (clock : A → ℝ≥0) (hclock : ∀ p, clock p ≤ H)
    (Z : ℕ → A → Ω → E)
    (hZ : ∀ n m p, ∀ᵐ ω ∂μ,
      (clock p : WithTop ℝ≥0) < τ n ω → (clock p : WithTop ℝ≥0) < τ m ω → Z n p ω = Z m p ω)
    (n : ℕ) (p : A) :
    ∀ᵐ ω ∂μ, (clock p : WithTop ℝ≥0) < τ n ω → value H τ escape Z p ω = Z n p ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ j k : ℕ,
      (clock p : WithTop ℝ≥0) < τ j ω → (clock p : WithTop ℝ≥0) < τ k ω → Z j p ω = Z k p ω :=
    ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun k ↦ hZ j k p
  filter_upwards [hall] with ω hω hn
  exact hω _ n ((WithTop.coe_le_coe.mpr (hclock p)).trans_lt (index_survives H τ escape ω)) hn

theorem bounded [CompactSpace A] (Z : ℕ → A → Ω → E)
    (hZ : ∀ n ω, Continuous (fun p ↦ Z n p ω)) (ω : Ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p, ‖value H τ escape Z p ω‖ ≤ K := by
  let f : C(A, E) := ⟨fun p ↦ value H τ escape Z p ω, continuous H τ escape Z hZ ω⟩
  exact ⟨‖f‖, norm_nonneg _, fun p ↦ f.norm_coe_le_norm p⟩

theorem initial_zero (μ : Measure Ω) (Z : ℕ → A → Ω → E) (initial : A → A)
    (hz : ∀ n, ∀ᵐ ω ∂μ, ∀ p, Z n (initial p) ω = 0) :
    ∀ᵐ ω ∂μ, ∀ p, value H τ escape Z (initial p) ω = 0 := by
  have hall := ae_all_iff.mpr hz
  exact hall.mono fun ω hω p ↦ hω _ p

include escape in
/-- Assemble continuous modifications of a compatible cutoff family.
The cutoff selection, common event and measurability proofs are shared
by the unit-time and arbitrary-horizon native convolution arguments. -/
theorem exists_of_modifications (μ : Measure Ω) (clock : A → ℝ≥0) (hclock : ∀ p, clock p≤H)
    (X : ℕ → A → Ω → E) (initial : A → A)
    (hv : ∀ n, ∃ Z : A → Ω → E, (∀ p, Measurable (Z p)) ∧
      (∀ p, Z p=ᵐ[μ] X n p) ∧ (∀ ω, Continuous (fun p ↦ Z p ω)) ∧ ∀ᵐ ω ∂μ, ∀ p, Z (initial p) ω=0)
    (hcompat : ∀ n m p, ∀ᵐ ω ∂μ, (clock p:WithTop ℝ≥0)<τ n ω →
      (clock p:WithTop ℝ≥0)<τ m ω → X n p ω=X m p ω)
    (hτ : ∀ n, MeasurableSet {ω | (H:WithTop ℝ≥0)<τ n ω}) :
    ∃ Y : A → Ω → E, (∀ p, Measurable (Y p)) ∧ (∀ ω, Continuous (fun p ↦ Y p ω)) ∧
      (∀ n p, ∀ᵐ ω ∂μ, (clock p:WithTop ℝ≥0)<τ n ω → Y p ω=X n p ω) ∧
      ∀ᵐ ω ∂μ, ∀ p, Y (initial p) ω=0 := by
  choose Z hZm hZe hZc hZzero using hv
  have hc (n m : ℕ) (p : A) : ∀ᵐ ω ∂μ, (clock p:WithTop ℝ≥0)<τ n ω →
      (clock p:WithTop ℝ≥0)<τ m ω → Z n p ω=Z m p ω := by
    filter_upwards [hZe n p,hZe m p,hcompat n m p] with ω hn hm hh hpn hpm
    exact hn.trans ((hh hpn hpm).trans hm.symm)
  refine ⟨value H τ escape Z,fun p ↦ measurable H τ escape Z p (fun n ↦ hZm n p) hτ,
    continuous H τ escape Z hZc,?_,initial_zero H τ escape μ Z initial hZzero⟩
  intro n p
  filter_upwards [agrees H τ escape μ clock hclock Z hc n p,hZe n p] with ω he hz hp
  exact (he hp).trans hz

end SHEStochastic.LocalizedFieldAssembly
