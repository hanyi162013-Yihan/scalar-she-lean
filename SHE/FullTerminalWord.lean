module

public import SHE.TerminalScoreChain
public import SHE.FullPredictablePhysicalWord
public import SHE.PhysicalFirstScore

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution
  PhysicalFirstScore
open scoped BigOperators
local instance fullTerminalWord_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- Literal all-order terminal first-score representation of the actual
physical recursive word. The terminal old profile is the same fixed
profile as in every earlier interval. Every old second score and the full
original root/centered-leaf product remain inside `oldAverage`; only the
residual intervals are combined. No chain, range, or covariance-split
assumption is left to the caller. -/
theorem terminal_first_score_ae (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ p, ell ≤ c p ∧ c p ≤ R.reference p)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ (lo : ℝ), 0 ≤ lo → lo < (carrier L k).terminal p →
      ∀ (v : StoppedFourier.CircleL2) (z : WordRecursion.State (n+k)),
      let Z := (carrier L k).observations.observations p
      let hi := (carrier L k).terminal p
      let A := intervalCovariance Z c lo hi
      let B := intervalCovariance Z (fun r => R.reference r-c r) lo hi
      let d := terminalDirection Z lo v
      fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference Z lo hi)
        (UncutSmoothWords.test L k p)) z d =
        ∫ old, ∫ residual, oldAverage L c k p (z+old+residual)*MeasurableGaussianScores.firstScore A d old
          ∂multivariateGaussian 0 (B+∑ j,covariances L Z (fun r => R.reference r-c r) k p j)
          ∂multivariateGaussian 0 A := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,hs,_,hphysical⟩ := hp
  intro lo hlo hgap v z
  let Z := (carrier L k).observations.observations p
  let hi := (carrier L k).terminal p
  let A := intervalCovariance Z c lo hi
  let B := intervalCovariance Z (fun r => R.reference r-c r) lo hi
  have hZ : ∀ i, (Z i).stop ≤ (Z i).target := RecursiveScoreSupport.carrier_ages L hages k p
  have hstop : ∀ i, hi ≤ (Z i).stop := (carrier L k).stops_after p
  have hcb (r : Domain) : ell ≤ c r ∧ c r ≤ R.upper :=
    ⟨(hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have hcn (r : Domain) : 0 ≤ c r ∧ c r ≤ R.upper :=
    ⟨hell.le.trans (hcb r).1,(hcb r).2⟩
  have hrn (r : Domain) : 0 ≤ R.reference r-c r ∧ R.reference r-c r ≤ R.upper :=
    ⟨sub_nonneg.mpr (hb r).2,(sub_le_self _ (hcn r).1).trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have ho : A.PosSemidef := interval_posSemidef Z hZ c hc hcn lo hi
  have hr : B.PosSemidef := interval_posSemidef Z hZ (fun r => R.reference r-c r)
    (R.reference_measurable.sub hc) hrn lo hi
  have hd : terminalDirection Z lo v ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) A).range :=
    terminalDirection_mem_range Z hlo hgap hstop hZ c hc hell hcb v
  have hsum := interval_add_profiles Z hZ c (fun r => R.reference r-c r) hc
    (R.reference_measurable.sub hc) R.upper_nonneg R.upper_nonneg
    (fun r => by rw [abs_of_nonneg (hcn r).1]; exact (hcn r).2)
    (fun r => by rw [abs_of_nonneg (hrn r).1]; exact (hrn r).2) lo hi
  have hsum' : intervalCovariance Z R.reference lo hi=A+B := by
    simpa only [add_sub_cancel] using hsum
  have he : intervalCovariance Z R.reference lo hi=WordRecursion.covariance R.reference Z lo hi :=
    PhysicalIntervalCovariance.interval_eq_covariance Z R.reference R.reference_measurable
      R.reference_bound hZ hstop hlo hgap.le
  have hfull : WordRecursion.covariance R.reference Z lo hi=A+B := he.symm.trans hsum'
  have h := chain.terminal_fderiv_reserved_score hs ho hr hd z
  have hFid : (fun w => UncutSmoothWords.test L k p (projection (fun i : Fin (n+k) => i) w))=
      UncutSmoothWords.test L k p := by
    rfl
  rw [hFid] at h
  have hold := SHE.PhysicalChainArrays.Physical.old_eq L Z c chain hphysical
  have hres := SHE.PhysicalChainArrays.Physical.residual_eq L Z c chain hphysical
  have hdir := SHE.PhysicalChainArrays.Physical.direction_eq L Z c chain hphysical
  have havg : chain.oldAverage=oldAverage L c k p := by
    unfold Chain.oldAverage oldAverage
    rw [hold,hdir,fullTest_eq_word L chain]
  rw [hres,havg] at h
  dsimp only
  rw [hfull]
  exact h

end SHE.PhysicalChainArrays
