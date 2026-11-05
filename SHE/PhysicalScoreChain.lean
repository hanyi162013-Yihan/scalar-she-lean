module

public import SHE.FixedOldScoreSupport
public import SHE.ScoreChainSupport
public import SHE.GaussianCoordinateRange

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  OldIntervalCovariance StoppedGaussianFeatures FixedOldScoreSupport
open scoped BigOperators Matrix.Norms.L2Operator
local instance physicalScoreChain_periodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

structure Selection (Z : Fin N → Observation) (k : ℕ) (p : History P k)
    (g : Fin (n+k) → Fin N) : Prop where
  observations : ∀ i, Z (g i) = (carrier L k).observations.observations p i
  omitted : ∀ j, j ∉ Set.range g → (Z j).stop ≤ (carrier L k).terminal p

theorem Selection.tail {Z : Fin N → Observation} {k : ℕ} {p : History P (k+1)}
    {g : Fin (n+k+1) → Fin N} (h : Selection L Z (k+1) p g) :
    Selection L Z k p.1 (fun i => g i.succ) := by
  refine ⟨fun i => h.observations i.succ, ?_⟩
  intro j hj
  by_cases hg : j ∈ Set.range g
  · obtain ⟨i, rfl⟩ := hg
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
    · have he := congrArg Observation.stop (h.observations 0)
      change (Z (g 0)).stop = (carrier L k).nodeTime p at he
      rw [he]
      exact ((carrier L k).nodeTime_mem p).2
    · exact False.elim (hj ⟨l, rfl⟩)
  · exact (h.omitted j hg).trans ((carrier L k).nodeTime_mem p).2

theorem Selection.omitted_tail {Z : Fin N → Observation} {k : ℕ} {p : History P (k+1)}
    {g : Fin (n+k+1) → Fin N} (h : Selection L Z (k+1) p g)
    (j : Fin N) (hj : j ∉ Set.range (fun i : Fin (n+k) => g i.succ)) :
    (Z j).stop ≤ (carrier L k).nodeTime p := by
  by_cases hg : j ∈ Set.range g
  · obtain ⟨i, rfl⟩ := hg
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
    · have he := congrArg Observation.stop (h.observations 0)
      exact he.le
    · exact False.elim (hj ⟨l, rfl⟩)
  · exact h.omitted j hg

def intervalCovariance (Z : Fin N → Observation) (c : Domain → ℝ) (lo hi : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  StoppedGaussianFeatures.stoppedCovariance (fun i => (Z i).stop) (fun i => (Z i).target)
    (fun i => (Z i).center) (intervalProfile c lo hi) 0

theorem stoppedRow_selected (Z : Fin N → Observation) (Z' : Fin n → Observation)
    (f : Fin n → Fin N) (h : ∀ i, Z (f i) = Z' i) (r : Domain) (i : Fin n) :
    StoppedGaussianFeatures.stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target)
      (fun i => (Z i).center) r (f i) =
    StoppedGaussianFeatures.stoppedRow (fun i => (Z' i).stop) (fun i => (Z' i).target)
      (fun i => (Z' i).center) r i := by
  simp only [StoppedGaussianFeatures.stoppedRow, h i]

theorem interval_submatrix (Z : Fin N → Observation) (Z' : Fin n → Observation)
    (f : Fin n → Fin N) (h : ∀ i, Z (f i) = Z' i) (c : Domain → ℝ) (lo hi : ℝ) :
    (intervalCovariance Z c lo hi).submatrix f f = intervalCovariance Z' c lo hi := by
  ext i j
  change (∫ r, intervalProfile c lo hi r *
    StoppedGaussianFeatures.stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) r (f i) *
    StoppedGaussianFeatures.stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target) (fun i => (Z i).center) r (f j)
    ∂StoppedGaussianFeatures.historyMeasure 0) = _
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    dsimp only
    rw [stoppedRow_selected Z Z' f h r i, stoppedRow_selected Z Z' f h r j])

def direction (Z : Fin N → Observation) (k : ℕ) (p : History P (k+1)) : WordRecursion.State N := by
  classical
  exact if Interior L k p then
    StoppedGaussianFeatures.stoppedRow (fun i => (Z i).stop) (fun i => (Z i).target)
      (fun i => (Z i).center) ((carrier L k).nodeTime p, p.2.2) else 0

theorem direction_projection {Z : Fin N → Observation} {k : ℕ} {p : History P (k+1)}
    {g : Fin (n+k+1) → Fin N} (h : Selection L Z (k+1) p g) :
    projection (fun i : Fin (n+k) => g i.succ) (direction L Z k p) = row L k p := by
  classical
  by_cases hp : Interior L k p
  · have htime : (carrier L k).nodeTime p = p.2.1 := ClippedCovariance.clip_eq ⟨hp.1.le, hp.2.le⟩
    ext i
    simp only [direction, row, hp, ite_true, projection_apply]
    change StoppedGaussianFeatures.stoppedRow _ _ _ _ (g i.succ) = _
    rw [stoppedRow_selected Z ((carrier L k).observations.observations p.1) _ h.tail.observations]
    have ht : (carrier L k).nodeTime p < ((carrier L k).observations.observations p.1 i).stop := by
      rw [htime]
      exact hp.2.trans_le ((carrier L k).stops_after p.1 i)
    simp only [StoppedGaussianFeatures.stoppedRow, heatRow, ite_eq_left ht]
  · simp only [direction, row, hp, ite_false, map_zero]

theorem direction_omitted {Z : Fin N → Observation} {k : ℕ} {p : History P (k+1)}
    {g : Fin (n+k+1) → Fin N} (h : Selection L Z (k+1) p g)
    (j : Fin N) (hj : j ∉ Set.range (fun i : Fin (n+k) => g i.succ)) :
    direction L Z k p j = 0 := by
  classical
  unfold direction
  split_ifs
  · have hs := Selection.omitted_tail L h j hj
    simp only [StoppedGaussianFeatures.stoppedRow, ite_eq_right (not_lt.mpr hs)]
  · rfl

def Before {Z : Fin N → Observation} {k : ℕ} {p : History P k} {g : Fin (n+k) → Fin N}
    (chain : Chain L k p g) : Prop :=
  ∀ i, (Z i).stop ≤ (carrier L k).terminal p → ∀ K ∈ chain.word.map Prod.fst,
    ∀ᵐ x ∂K.measure, K.shift x i = 0

/-- The full interval data are retained in the chain, so later covariance
coherence and moment estimates refer to the actual physical old fractions. -/
def Physical (Z : Fin N → Observation) (c : Domain → ℝ) :
    {k : ℕ} → {p : History P k} → {g : Fin (n+k) → Fin N} → Chain L k p g → Prop
  | _, _, _, .root _ _ => True
  | _, _, _, .step k p _ _ prev _ old residual _ _ _ d _ _ =>
      Physical Z c prev ∧
      old = intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1) ∧
      residual = intervalCovariance Z (fun z => R.reference z - c z)
        ((carrier L k).nodeTime p) ((carrier L k).terminal p.1) ∧ d = direction L Z k p

/-- A physical final-space score chain, with all original stop masks and
both actual old/residual interval covariances. Its coordinate support is
derived from the time ordering, rather than supplied as a word premise. -/
theorem exists_chain (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N) (hsel : Selection L Z k p g)
    (hsup : RecursiveGaussianScores.Supported L (profileCovariances L c)
      (profileCovariances L (fun p => R.reference p - c p)) k p) :
    ∃ chain : Chain L k p g, chain.CoordinateSupport ∧ Before L (Z := Z) chain ∧ Physical L Z c chain := by
  induction k with
  | zero =>
    refine ⟨.root p g, trivial, ?_, trivial⟩
    intro i hi K hK
    simp only [Chain.word, List.map_nil, List.not_mem_nil] at hK
  | succ k ih =>
    let f : Fin (n+k) → Fin N := fun i => g i.succ
    let lo := (carrier L k).nodeTime p
    let hi := (carrier L k).terminal p.1
    let old := intervalCovariance Z c lo hi
    let residual := intervalCovariance Z (fun p => R.reference p - c p) lo hi
    let d := direction L Z k p
    obtain ⟨prev, hprev, hbefore, hphysical⟩ := ih p.1 f hsel.tail hsup.1
    have hc0 (z : Domain) : 0 ≤ c z ∧ c z ≤ R.upper :=
      ⟨hell.le.trans (hb z).1, (hb z).2.trans ((le_abs_self _).trans (R.reference_bound z))⟩
    have hr0 (z : Domain) : 0 ≤ R.reference z - c z ∧ R.reference z - c z ≤ R.upper :=
      ⟨sub_nonneg.mpr (hb z).2, (sub_le_self _ (hc0 z).1).trans ((le_abs_self _).trans (R.reference_bound z))⟩
    have ho : old.PosSemidef := covariance_posSemidef _ _ _ hZ c hc hc0 lo hi
    have hr : residual.PosSemidef := covariance_posSemidef _ _ _ hZ _ (R.reference_measurable.sub hc) hr0 lo hi
    have hold : old.submatrix f f = profileCovariances L c k p := by
      rw [interval_submatrix Z ((carrier L k).observations.observations p.1) f hsel.tail.observations]
      exact PhysicalIntervalCovariance.interval_eq_covariance _ c hc
        (fun z => by rw [abs_of_nonneg (hc0 z).1]; exact (hc0 z).2)
        (RecursiveScoreSupport.carrier_ages L hages k p.1) ((carrier L k).stops_after p.1)
        (R.base_nonneg.trans ((carrier L k).nodeTime_mem p).1) ((carrier L k).nodeTime_mem p).2
    have hres : residual.submatrix f f = profileCovariances L (fun p => R.reference p - c p) k p := by
      rw [interval_submatrix Z ((carrier L k).observations.observations p.1) f hsel.tail.observations]
      exact PhysicalIntervalCovariance.interval_eq_covariance _ _ (R.reference_measurable.sub hc)
        (fun z => by
          change |R.reference z - c z| ≤ R.upper
          rw [abs_of_nonneg (hr0 z).1]
          exact (hr0 z).2)
        (RecursiveScoreSupport.carrier_ages L hages k p.1) ((carrier L k).stops_after p.1)
        (R.base_nonneg.trans ((carrier L k).nodeTime_mem p).1) ((carrier L k).nodeTime_mem p).2
    have hcov : (old + residual).submatrix f f = ((carrier L k).nodeCovariance p).val := by
      change old.submatrix f f + residual.submatrix f f = _
      rw [hold, hres]
      exact hsup.2.2.2.1.symm
    have hd : projection f d = row L k p := direction_projection L hsel
    have hrg : d ∈ (Matrix.toEuclideanCLM (𝕜 := ℝ) old).range := by
      apply GaussianCoordinateRange.range_lift old f d
      · intro i hi j
        exact covariance_inactive_row _ _ _ c lo _ i j (Selection.omitted_tail L hsel i hi)
      · exact direction_omitted L hsel
      · rw [hold, hd]
        exact hsup.2.2.2.2
    let chain : Chain L (k+1) p g := .step k p f g prev (fun _ => rfl) old residual ho hr hcov d hd hrg
    have hzero (i : Fin N) (hs : (Z i).stop ≤ lo) :
        ∀ᵐ x ∂(GaussianTriangularKernel.kernel old residual d).measure,
          (GaussianTriangularKernel.kernel old residual d).shift x i = 0 :=
      GaussianTriangularKernel.coordinate_support_of_zero_rows ho hr d i
        (fun j => covariance_inactive_row _ _ _ c lo hi i j hs)
        (fun j => covariance_inactive_row _ _ _ _ lo hi i j hs)
    have hhead : (Z (g 0)).stop = lo := congrArg Observation.stop (hsel.observations 0)
    refine ⟨chain, ⟨hprev, ?_⟩, ?_, hphysical, rfl, rfl, rfl⟩
    · intro K hK
      simp only [List.map_cons, List.mem_cons] at hK
      rcases hK with rfl | hK
      · exact hzero (g 0) hhead.le
      · exact hbefore (g 0) (hhead.le.trans ((carrier L k).nodeTime_mem p).2) K hK
    · intro i hs K hK
      change K ∈ (GaussianTriangularKernel.kernel old residual d :: prev.word.map Prod.fst) at hK
      simp only [List.mem_cons] at hK
      rcases hK with rfl | hK
      · exact hzero i hs
      · exact hbefore i (hs.trans ((carrier L k).nodeTime_mem p).2) K hK

/-- Every finite physical history admits the actual common final-space
Gaussian chain almost everywhere. All covariance splits, physical range
conditions and triangular support have been proved from the elliptic old
profile and the original observation geometry. -/
theorem exists_chain_ae (c : Domain → ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0 < ell)
    (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∃ chain : Chain L k p (fun i => i), chain.CoordinateSupport ∧
        Before L (Z := (carrier L k).observations.observations p) chain ∧
        Physical L ((carrier L k).observations.observations p) c chain := by
  filter_upwards [FixedOldScoreSupport.supported_ae L c hc hell hb hages μ k] with p hp
  apply exists_chain L c hc hell hb hages ((carrier L k).observations.observations p)
    (RecursiveScoreSupport.carrier_ages L hages k p) k p (fun i => i) _ hp
  exact ⟨fun _ => rfl, fun j hj => False.elim (hj ⟨j, rfl⟩)⟩

end SHE.PhysicalScoreChain
