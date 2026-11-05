module

public import SHE.ScoreProjectionEnergy
public import SHE.PhysicalChainArrays

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianCoordinates FixedOldScoreSupport OldIntervalCovariance
  MeasurableGaussianScores ScoreProjectionEnergy
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The literal old score energy in the final growing frame equals its
energy in the original earlier frame, before subsequent spatial choices.
All omitted covariance rows and physical direction coordinates vanish. -/
theorem node_scoreVariance_eq (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {M : ℝ} (hb : ∀ r, 0 ≤ c r ∧ c r ≤ M)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    {k : ℕ} {p : History P (k+1)} (Z : Fin N → Observation)
    (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (g : Fin (n+k+1) → Fin N) (hg : Function.Injective g)
    (hsel : Selection L Z (k+1) p g)
    (hrange : row L k p ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (profileCovariances L c k p)).range) :
    scoreVariance (intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1))
      (direction L Z k p) = scoreVariance (profileCovariances L c k p) (row L k p) := by
  let A := intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1)
  let f : Fin (n+k) → Fin N := fun i => g i.succ
  have hA : A.PosSemidef := covariance_posSemidef _ _ _ hZ c hc hb _ _
  have hrows : ∀ i, i ∉ Set.range f → ∀ j, A i j=0 := by
    intro i hi j
    exact covariance_inactive_row _ _ _ c _ _ i j (Selection.omitted_tail L hsel i hi)
  have hcols : ∀ i, i ∉ Set.range f → ∀ j, A j i=0 := by
    intro i hi j
    have he := congrArg (fun B : Matrix (Fin N) (Fin N) ℝ => B i j) hA.isHermitian.eq
    have he' : A j i=A i j := by simpa only [Matrix.conjTranspose_apply,star_trivial] using he
    exact he'.trans (hrows i hi j)
  have hM : 0 ≤ M := (hb (0,0)).1.trans (hb (0,0)).2
  have hrestrict : A.submatrix f f=profileCovariances L c k p := by
    rw [interval_submatrix Z ((carrier L k).observations.observations p.1) f hsel.tail.observations]
    exact PhysicalIntervalCovariance.interval_eq_covariance _ c hc
      (fun z => by rw [abs_of_nonneg (hb z).1]; exact (hb z).2)
      (RecursiveScoreSupport.carrier_ages L hages k p.1) ((carrier L k).stops_after p.1)
      (R.base_nonneg.trans ((carrier L k).nodeTime_mem p).1) ((carrier L k).nodeTime_mem p).2
  have hd : projection f (direction L Z k p)=row L k p := direction_projection L hsel
  have hdz : ∀ i, i ∉ Set.range f → direction L Z k p i=0 := direction_omitted L hsel
  have hdfull : direction L Z k p ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) A).range := by
    apply GaussianCoordinateRange.range_lift A f _ hrows hdz
    rw [hrestrict,hd]
    exact hrange
  have hh := scoreVariance_projection f (hg.comp (Fin.succ_injective _)) hA hcols hdfull hdz
  rw [hrestrict,hd] at hh
  exact hh

end SHE.PhysicalScoreChain
