module

public import SHE.PhysicalChainCovariance

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures FixedOldScoreSupport
open scoped BigOperators Matrix.Norms.L2Operator
local instance physicalChainArrays_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def lower : (k : ℕ) → History P k → Fin k → ℝ
  | 0 => fun _ => Fin.elim0
  | k+1 => fun p => Fin.cases ((carrier L k).nodeTime p) (lower k p.1)

def upper : (k : ℕ) → History P k → Fin k → ℝ
  | 0 => fun _ => Fin.elim0
  | k+1 => fun p => Fin.cases ((carrier L k).terminal p.1) (upper k p.1)

def space : (k : ℕ) → History P k → Fin k → HeatCircle
  | 0 => fun _ => Fin.elim0
  | k+1 => fun p => Fin.cases p.2.2 (space k p.1)

def covariances (Z : Fin N → Observation) (c : Domain → ℝ) (k : ℕ) (p : History P k) :
    Fin k → Matrix (Fin N) (Fin N) ℝ :=
  fun j => intervalCovariance Z c (lower L k p j) (upper L k p j)

def directions (Z : Fin N → Observation) : (k : ℕ) → History P k → Fin k → WordRecursion.State N
  | 0 => fun _ => Fin.elim0
  | k+1 => fun p => Fin.cases (PhysicalScoreChain.direction L Z k p) (directions Z k p.1)

def leafIndex : (k : ℕ) → (Fin (n+k) → Fin N) → Fin k → Fin N
  | 0 => fun _ => Fin.elim0
  | k+1 => fun g => Fin.cases (g 0) (leafIndex k (fun i => g i.succ))

def rootSelector : (k : ℕ) → (Fin (n+k) → Fin N) → Fin n → Fin N
  | 0 => fun g => g
  | k+1 => fun g => rootSelector k (fun i => g i.succ)

def initial (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N) (z : WordRecursion.State N) : ℝ :=
  L.test (rootParameter k p) (projection (rootSelector k g) z)

def baseline (k : ℕ) (p : History P k) (j : Fin k) : ℝ :=
  R.reference (lower L k p j, space k p j)

def leaves (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N)
    (j : Fin k) (z : WordRecursion.State N) : ℝ :=
  (1/2:ℝ) * (R.totalVariance (z (leafIndex k g j)) - baseline L k p j)

theorem lower_measurable (k : ℕ) (j : Fin k) : Measurable (fun p : History P k => lower L k p j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (carrier L k).nodeTime_measurable
    · exact (ih i).comp measurable_fst

theorem upper_measurable (k : ℕ) (j : Fin k) : Measurable (fun p : History P k => upper L k p j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (carrier L k).terminal_measurable.comp measurable_fst
    · exact (ih i).comp measurable_fst

theorem space_measurable (k : ℕ) (j : Fin k) : Measurable (fun p : History P k => space k p j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · exact measurable_snd.snd
    · exact (ih i).comp measurable_fst

theorem rootParameter_measurable (k : ℕ) : Measurable (rootParameter (P := P) k) := by
  induction k with
  | zero => exact measurable_id
  | succ k ih => exact ih.comp measurable_fst

theorem baseline_measurable (k : ℕ) (j : Fin k) : Measurable (fun p : History P k => baseline L k p j) :=
  R.reference_measurable.comp ((lower_measurable L k j).prodMk (space_measurable k j))

theorem initial_measurable (k : ℕ) (g : Fin (n+k) → Fin N) :
    Measurable (fun p : History P k × WordRecursion.State N => initial L k p.1 g p.2) :=
  L.test_measurable.comp (((rootParameter_measurable k).comp measurable_fst).prodMk
    ((projection (rootSelector k g)).measurable.comp measurable_snd))

theorem leaves_measurable (k : ℕ) (g : Fin (n+k) → Fin N) (j : Fin k) :
    Measurable (fun p : History P k × WordRecursion.State N => leaves L k p.1 g j p.2) :=
  measurable_const.mul ((R.totalVariance_smooth.smooth.continuous.measurable.comp
    (((WithLp.measurable_ofLp 2 (Fin N → ℝ)).comp measurable_snd).eval)).sub
      ((baseline_measurable L k j).comp measurable_fst))

/-- Deterministic old matrices and directions do not depend on the choice
of the proof-bearing physical chain. -/
theorem Physical.old_eq (Z : Fin N → Observation) (c : Domain → ℝ)
    {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g)
    (hp : Physical L Z c chain) : chain.old = covariances L Z c k p := by
  induction chain with
  | root p f => exact funext (fun j => Fin.elim0 j)
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    obtain ⟨hprev, he, _, _⟩ := hp
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact he
    · exact congrFun (ih hprev) i

theorem Physical.residual_eq (Z : Fin N → Observation) (c : Domain → ℝ)
    {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g)
    (hp : Physical L Z c chain) :
    chain.residual = covariances L Z (fun z => R.reference z - c z) k p := by
  induction chain with
  | root p f => exact funext (fun j => Fin.elim0 j)
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    obtain ⟨hprev, _, he, _⟩ := hp
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact he
    · exact congrFun (ih hprev) i

theorem Physical.direction_eq (Z : Fin N → Observation) (c : Domain → ℝ)
    {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g)
    (hp : Physical L Z c chain) : chain.direction = directions L Z k p := by
  induction chain with
  | root p f => exact funext (fun j => Fin.elim0 j)
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    obtain ⟨hprev, _, _, he⟩ := hp
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact he
    · exact congrFun (ih hprev) i

theorem chain_leaves_eq {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g) :
    chain.leaves = leaves L k p g := by
  induction chain with
  | root p f => exact funext (fun j => Fin.elim0 j)
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    have he : (fun i => g i.succ) = f := funext ht
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change prev.leaves i = leaves L k p.1 (fun j => g j.succ) i
      rw [he]
      exact congrFun ih i

theorem chain_initial_eq {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N} (chain : Chain L k p g) :
    chain.initial = initial L k p g := by
  induction chain with
  | root p f => rfl
  | step k p f g prev ht old residual ho hr hcov d hd hrg ih =>
    change prev.initial = initial L k p.1 (fun i => g i.succ)
    rw [funext ht]
    exact ih

section MeasurableFields
variable {X : Type*} [MeasurableSpace X]

/-- Jointly Borel old/residual arrays for variable physical histories,
variable original observation lists, and variable coefficient profiles. -/
theorem covariances_measurable (Z : VariableObservations.Family X N)
    (c : X × Domain → ℝ) (hc : Measurable c) (k : ℕ)
    (h : X → History P k) (hh : Measurable h) (j : Fin k) :
    Measurable (fun x => covariances L (Z.observations x) (fun p => c (x,p)) k (h x) j) := by
  let S : Set (X × Domain) := {p | lower L k (h p.1) j < p.2.1 ∧ p.2.1 ≤ upper L k (h p.1) j}
  have hS : MeasurableSet S :=
    (measurableSet_lt (((lower_measurable L k j).comp hh).comp measurable_fst) measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst (((upper_measurable L k j).comp hh).comp measurable_fst))
  have hm := StoppedGaussianFields.covariance_measurable Z (hc.indicator hS) (measurable_const (a := (0:ℝ)))
  convert! hm using 1
  funext x
  unfold covariances intervalCovariance StoppedGaussianFields.covariance
  congr 1
  funext p
  simp only [intervalProfile, timeSet, Set.indicator, mem_prod, mem_Ioc, mem_univ, and_true, S, mem_setOf_eq]

theorem directions_measurable (Z : VariableObservations.Family X N) (k : ℕ)
    (h : X → History P k) (hh : Measurable h) (j : Fin k) :
    Measurable (fun x => directions L (Z.observations x) k (h x) j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · have hm := StoppedGaussianFields.row_measurable Z |>.comp
        (measurable_id.prodMk ((((carrier L k).nodeTime_measurable.comp hh).prodMk (measurable_snd.snd.comp hh))))
      exact hm.ite ((interior_measurableSet L k).preimage hh) measurable_const
    · exact ih (fun x => (h x).1) (measurable_fst.comp hh) i

end MeasurableFields
end SHE.PhysicalChainArrays
