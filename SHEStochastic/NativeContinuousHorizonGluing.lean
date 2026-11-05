module

public import SHEStochastic.FiniteScalarIto
public import SHEStochastic.ConditionalCharacteristic
public import SHE.NullCompleteFiltration
public import BrownianMotion.Continuity.KolmogorovChentsov
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeContinuousHorizonGluing
open MeasureTheory ProbabilityTheory SHE Set
open scoped NNReal ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]

def horizon (j : ℕ) : ℝ≥0 := j+1

theorem covering (t : ℝ≥0) : t ≤ horizon ⌈t⌉₊ :=
  (Nat.le_ceil t).trans (by dsimp [horizon]; exact le_add_of_nonneg_right (by norm_num))

variable (Q : ∀ j : ℕ,FiniteScalarIto.Family F μ (horizon j) ι)

def Good (ω : Ω) : Prop := ∀ i j k t,t ≤ min (horizon j) (horizon k) → (Q j).W i t ω=(Q k).W i t ω

/-- Countably many continuous finite-horizon versions agree on one
common event of full probability, simultaneously at every real time. -/
theorem good_ae
    (hQ : ∀ i j k t,t ≤ min (horizon j) (horizon k) → (Q j).W i t =ᵐ[μ] (Q k).W i t) :
    ∀ᵐ ω ∂μ,Good Q ω := by
  have ha (i : ι) (j k : ℕ) : ∀ᵐ ω ∂μ,∀ t : ℝ≥0,
      (Q j).W i (min t (min (horizon j) (horizon k))) ω=
      (Q k).W i (min t (min (horizon j) (horizon k))) ω := by
    have hh := indistinguishable_of_edist_modification
      (Filter.Eventually.of_forall fun ω => ((Q j).continuous i ω).comp
        (continuous_id.min (continuous_const (y := min (horizon j) (horizon k)))))
      (Filter.Eventually.of_forall fun ω => ((Q k).continuous i ω).comp
        (continuous_id.min (continuous_const (y := min (horizon j) (horizon k)))))
      (fun t => (hQ i j k (min t (min (horizon j) (horizon k))) (min_le_right _ _)).mono
        (fun ω h => by
          change edist ((Q j).W i (min t (min (horizon j) (horizon k))) ω)
            ((Q k).W i (min t (min (horizon j) (horizon k))) ω)=0
          rw [h,edist_self]))
    filter_upwards [hh] with ω hω t
    exact edist_eq_zero.mp (hω t)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => ha i j k)))]
    with ω hω i j k t ht
  simpa only [min_eq_left ht] using hω i j k t

/-- The exceptional set is sent to the zero path. On the common full
probability event every finite-horizon version supplies the same path. -/
def value (i : ι) (t : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if Good Q ω then (Q ⌈t⌉₊).W i t ω else 0

theorem value_eq (ω : Ω) (hω : Good Q ω) (i : ι) (j : ℕ) (t : ℝ≥0) (ht : t ≤ horizon j) :
    value Q i t ω=(Q j).W i t ω := by
  classical
  rw [value,if_pos hω]
  exact hω i _ j t (le_min (covering t) ht)

theorem continuous (i : ι) (ω : Ω) : Continuous (fun t => value Q i t ω) := by
  classical
  by_cases hω : Good Q ω
  · rw [continuous_iff_continuousAt]
    intro t
    let j : ℕ := ⌈t⌉₊+1
    have ht : t<horizon j := lt_of_le_of_lt (covering t) (by dsimp [horizon,j];push_cast;linarith)
    apply ((Q j).continuous i ω).continuousAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact value_eq Q ω hω i j s hs.le
  · have he : (fun t => value Q i t ω)=fun _ => (0 : ℝ) := by
      funext t
      exact if_neg hω
    rw [he]
    exact continuous_const

variable (hQ : ∀ i j k t,t ≤ min (horizon j) (horizon k) → (Q j).W i t =ᵐ[μ] (Q k).W i t)

include hQ in
theorem version (i : ι) (j : ℕ) (t : ℝ≥0) (ht : t ≤ horizon j) :
    value Q i t =ᵐ[μ] (Q j).W i t := by
  filter_upwards [good_ae Q hQ] with ω hω
  exact value_eq Q ω hω i j t ht

/-- The glued coordinates form one actual global Brownian process in
the original completed filtration. Every horizon uses literally the
same coordinate paths. -/
def family (hnull : NullCompleteFiltration.ContainsNullSets F μ) (H : ℝ≥0) :
    FiniteScalarIto.Family F μ H ι where
  W := value Q
  continuous := continuous Q
  adapted i t :=
    (NullCompleteFiltration.stronglyMeasurable_congr F μ hnull t
      ((Q ⌈t⌉₊).adapted i t).stronglyMeasurable (version Q hQ i ⌈t⌉₊ t (covering t))).measurable
  law n a := by
    let j : ℕ := ⌈H⌉₊
    constructor
    · intro times ht
      apply (((Q j).law n a).1 times (fun i => (ht i).trans (covering H))).congr
      filter_upwards [ae_all_iff.mpr (fun i : Fin n => version Q hQ (a i) j (times i) ((ht i).trans (covering H)))] with ω hω
      apply PiLp.ext
      intro i
      exact hω i
    · intro s t hst ht
      have he : (fun ω => WithLp.toLp 2 (fun i : Fin n => value Q (a i) t ω-value Q (a i) s ω)) =ᵐ[μ]
          fun ω => WithLp.toLp 2 (fun i : Fin n => (Q j).W (a i) t ω-(Q j).W (a i) s ω) := by
        filter_upwards [ae_all_iff.mpr (fun i : Fin n => version Q hQ (a i) j t (ht.trans (covering H))),
          ae_all_iff.mpr (fun i : Fin n => version Q hQ (a i) j s ((hst.trans ht).trans (covering H)))] with ω hti hsi
        apply PiLp.ext
        intro i
        exact congrArg₂ (·-·) (hti i) (hsi i)
      have hh := ConditionalCharacteristic.indep_comap_congr (F s) he
        (by simpa only [BorelSpace.measurable_eq] using ((Q j).law n a).2 s t hst (ht.trans (covering H)))
      simpa only [BorelSpace.measurable_eq] using hh

end SHEStochastic.NativeContinuousHorizonGluing
