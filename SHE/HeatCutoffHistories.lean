module

public import SHE.CutoffWordStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u

namespace SHE.HeatCutoffHistories
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords
open Classical
variable {P : Type u} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}

def Gap (L : Level R P n) (ε : ℝ) : Prop :=
  ∀ p i,ε ≤ (L.observations.observations p i).target-L.terminal p

namespace Level
variable (L : CutoffWordLevel.Level R P n)

/-- The inserted stop is unchanged; only its target is advanced by the
separate spatial heat-regularization age ε. -/
def heatChildObservations (ε : ℝ) : VariableObservations.Family (P × (ℝ × HeatCircle)) (n+1) where
  observations := fun p => Fin.cases ⟨L.nodeTime p,L.nodeTime p+ε,p.2.2⟩
    (L.observations.observations p.1)
  stop_measurable := by
    intro i
    refine Fin.cases L.nodeTime_measurable (fun j => ?_) i
    exact (L.observations.stop_measurable j).comp measurable_fst
  target_measurable := by
    intro i
    refine Fin.cases (L.nodeTime_measurable.add_const ε) (fun j => ?_) i
    exact (L.observations.target_measurable j).comp measurable_fst
  center_measurable := by
    intro i
    refine Fin.cases measurable_snd.snd (fun j => ?_) i
    exact (L.observations.center_measurable j).comp measurable_fst

def heatExtend (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    CutoffWordLevel.Level R (P × (ℝ × HeatCircle)) (n+1) where
  observations := heatChildObservations L ε
  terminal := L.nodeTime
  terminal_measurable := L.nodeTime_measurable
  terminal_base := fun p => (L.nodeTime_mem p).1
  terminal_horizon := fun p => (L.nodeTime_mem p).2.trans (L.terminal_horizon p.1)
  targets_after := by
    intro p i
    refine Fin.cases (le_add_of_nonneg_right hε) (fun j => ?_) i
    exact (L.nodeTime_mem p).2.trans (L.targets_after p.1 j)
  stops_after := by
    intro p i
    refine Fin.cases le_rfl (fun j => ?_) i
    exact (L.nodeTime_mem p).2.trans (L.stops_after p.1 j)
  test := L.childTest δ
  test_uniform := L.childTest_uniform hδ
  test_measurable := L.childTest_measurable δ

theorem heatExtend_gap {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) (hgap : Gap L ε) :
    Gap (heatExtend L δ ε hδ hε) ε := by
  intro p i
  refine Fin.cases ?_ (fun j => ?_) i
  · change ε ≤ L.nodeTime p+ε-L.nodeTime p
    linarith
  · change ε ≤ (L.observations.observations p.1 j).target-L.nodeTime p
    linarith [(hgap p.1 j),(L.nodeTime_mem p).2]

theorem heatChild_head (ε : ℝ) (hε : 0 < ε)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) (p : P × (ℝ × HeatCircle)) :
    observe U X ((heatChildObservations L ε).observations p) (L.nodeTime p) 0 =
      PhysicalProfile.physicalHeatMean (U (L.nodeTime p)) (ε,p.2.2) := by
  change (if L.nodeTime p < L.nodeTime p+ε then
    PhysicalProfile.physicalHeatMean (U (L.nodeTime p)) (L.nodeTime p+ε-L.nodeTime p,p.2.2)
    else X (L.nodeTime p,p.2.2)) = _
  rw [if_pos (by linarith)]
  congr 2
  ring

theorem heatChild_tail (ε : ℝ) (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ)
    (p : P × (ℝ × HeatCircle)) :
    tailProjection n (observe U X ((heatChildObservations L ε).observations p) (L.nodeTime p)) =
      observe U X (L.observations.observations p.1) (L.nodeTime p) := by
  ext i
  rfl

end Level

def iterate (L : CutoffWordLevel.Level R P n) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    (k : ℕ) → CutoffWordLevel.Level R (History P k) (n+k)
  | 0 => L
  | k+1 => HeatCutoffHistories.Level.heatExtend (iterate L δ ε hδ hε k) δ ε hδ hε

theorem iterate_gap (L : CutoffWordLevel.Level R P n) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hgap : Gap L ε) (k : ℕ) : Gap (iterate L δ ε hδ hε k) ε := by
  induction k with
  | zero => exact hgap
  | succ k ih => exact HeatCutoffHistories.Level.heatExtend_gap _ hδ hε ih

end SHE.HeatCutoffHistories
