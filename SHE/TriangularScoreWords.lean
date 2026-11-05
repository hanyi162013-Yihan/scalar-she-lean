module

public import SHE.WeightedBorelAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.TriangularScoreWords
open Set MeasureTheory ProbabilityTheory GaussianIncrement
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- An actual integrable translation kernel. In the physical word its
source consists of an old Gaussian vector and a residual Gaussian vector;
its weight is the old centered-square score. -/
structure Kernel (X : Type*) [MeasurableSpace X] (n : ℕ) where
  measure : Measure X
  sigmaFinite : SigmaFinite measure
  score : X → ℝ
  score_measurable : Measurable score
  score_integrable : Integrable score measure
  shift : X → State n
  shift_measurable : Measurable shift

attribute [instance] Kernel.sigmaFinite

def Kernel.action (K : Kernel X n) (F : State n → ℝ) : State n → ℝ :=
  WeightedBorelAverage.average K.measure K.score K.shift F

/-- The physical support statement needed for a multiplier to commute
past a score kernel. It is an almost-everywhere condition on the actual
law, and does not assert independence of coordinate observations. -/
def Kernel.Invariant (K : Kernel X n) (G : State n → ℝ) : Prop :=
  ∀ z, ∀ᵐ x ∂K.measure, G (z + K.shift x) = G z

theorem Kernel.action_mul_invariant (K : Kernel X n) (G F : State n → ℝ)
    (hG : K.Invariant G) (z : State n) :
    K.action (fun y => G y * F y) z = G z * K.action F z := by
  change (∫ x, K.score x * (G (z + K.shift x) * F (z + K.shift x)) ∂K.measure) = _
  calc
    _ = ∫ x, G z * (K.score x * F (z + K.shift x)) ∂K.measure := by
      apply integral_congr_ae
      filter_upwards [hG z] with x hx
      rw [hx]
      ring
    _ = _ := integral_const_mul _ _

def actions (ks : List (Kernel X n)) (F : State n → ℝ) : State n → ℝ :=
  ks.foldr Kernel.action F

theorem actions_mul_invariant (ks : List (Kernel X n)) (G F : State n → ℝ)
    (hG : ∀ K ∈ ks, K.Invariant G) :
    actions ks (fun y => G y * F y) = fun z => G z * actions ks F z := by
  induction ks with
  | nil => rfl
  | cons K ks ih =>
    change K.action (actions ks (fun y => G y * F y)) = _
    rw [ih (fun Q hQ => hG Q (List.mem_cons_of_mem _ hQ))]
    funext z
    exact K.action_mul_invariant G (actions ks F) (hG K (List.mem_cons_self)) z

abbrev Word (X : Type*) [MeasurableSpace X] (n : ℕ) := List (Kernel X n × (State n → ℝ))

def apply (word : Word X n) (F : State n → ℝ) : State n → ℝ :=
  word.foldr (fun p H z => p.2 z * p.1.action H z) F

def fullTest (word : Word X n) (F : State n → ℝ) : State n → ℝ :=
  word.foldr (fun p H z => p.2 z * H z) F

/-- Later leaves are constant along every earlier physical interval
increment, including their own interval. Older leaves can remain fully
correlated with every older Gaussian coordinate. -/
def Triangular : Word X n → Prop
  | [] => True
  | p :: word => Triangular word ∧ ∀ K ∈ (p :: word).map Prod.fst, K.Invariant p.2

/-- Exact all-order removal of the interleaved leaf multipliers. Every
leaf and baseline occurs once in the common shifted full product. -/
theorem apply_eq_actions_fullTest (word : Word X n) (hword : Triangular word)
    (F : State n → ℝ) :
    apply word F = actions (word.map Prod.fst) (fullTest word F) := by
  induction word with
  | nil => rfl
  | cons p word ih =>
    obtain ⟨htail, hinv⟩ := hword
    have htailinv : ∀ K ∈ word.map Prod.fst, K.Invariant p.2 :=
      fun K hK => hinv K (List.mem_cons_of_mem _ hK)
    have hi := ih htail
    change (fun z => p.2 z * p.1.action (apply word F) z) =
      p.1.action (actions (word.map Prod.fst) (fun z => p.2 z * fullTest word F z))
    rw [actions_mul_invariant _ _ _ htailinv, hi]
    funext z
    exact (p.1.action_mul_invariant p.2 (actions (word.map Prod.fst) (fullTest word F))
      (hinv p.1 (List.mem_cons_self)) z).symm

end SHE.TriangularScoreWords
