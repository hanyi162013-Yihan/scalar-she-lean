module

public import SHE.CutoffWordLevel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual finite history spaces and finite product measures for the
recursive cutoff words. Every derivative and Borel property is obtained
from the recursive construction, rather than assumed at later levels. -/
noncomputable section
universe u
namespace SHE.CutoffWordHistories
open Set MeasureTheory StoppedFourier CutoffWordLevel
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def History (P : Type u) : ℕ → Type u
  | 0 => P
  | k+1 => History P k × (ℝ × HeatCircle)

instance historyMeasurableSpace (P : Type u) [MeasurableSpace P] (k : ℕ) : MeasurableSpace (History P k) :=
  match k with
  | 0 => inferInstanceAs (MeasurableSpace P)
  | k+1 => @Prod.instMeasurableSpace (History P k) (ℝ × HeatCircle)
      (historyMeasurableSpace P k) inferInstance

def nodeMeasure (R : ReferenceData) : Measure (ℝ × HeatCircle) :=
  (volume.restrict (Ioc R.base R.horizon)).prod AddCircle.haarAddCircle

instance nodeMeasure_finite (R : ReferenceData) : IsFiniteMeasure (nodeMeasure R) :=
  inferInstanceAs (IsFiniteMeasure ((volume.restrict (Ioc R.base R.horizon)).prod AddCircle.haarAddCircle))

def historyMeasure {P : Type u} [MeasurableSpace P] (R : ReferenceData) (μ : Measure P) :
    (k : ℕ) → Measure (History P k)
  | 0 => μ
  | k+1 => (historyMeasure R μ k).prod (nodeMeasure R)

instance historyMeasure_finite {P : Type u} [MeasurableSpace P] (R : ReferenceData)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) : IsFiniteMeasure (historyMeasure R μ k) := by
  induction k with
  | zero => exact inferInstanceAs (IsFiniteMeasure μ)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (IsFiniteMeasure ((historyMeasure R μ k).prod (nodeMeasure R)))

def iterate {P : Type u} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
    (L : Level R P n) (δ : ℝ) (hδ : 0 < δ) : (k : ℕ) → Level R (History P k) (n+k)
  | 0 => L
  | k+1 => (iterate L δ hδ k).extend δ hδ

/-- Each test is the literal recursively extended Gaussian/insertion
word. All finite history levels have uniform bounds for every derivative. -/
theorem iterate_uniform {P : Type u} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
    (L : Level R P n) (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    UniformSmooth.UniformBoundedSmooth (iterate L δ hδ k).test :=
  (iterate L δ hδ k).test_uniform

theorem iterate_measurable {P : Type u} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
    (L : Level R P n) (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    Measurable (fun p : History P k × WordRecursion.State (n+k) => (iterate L δ hδ k).test p.1 p.2) :=
  (iterate L δ hδ k).test_measurable

end SHE.CutoffWordHistories
