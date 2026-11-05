module

public import SHE.PhysicalTerminalAssignments
public import SHE.CoveredControlledLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  PhysicalFirstScore
open scoped BigOperators
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The literal recursive terminal score formula for any direction in
the actual fresh old covariance range. In particular the direction may
be a physical point heat row, retaining the input/output kernel. -/
theorem terminal_range_first_score_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ lo : ℝ,0≤lo → lo<(carrier L k).terminal p →
      ∀ (d z : WordRecursion.State (n+k)),
      d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance
        ((carrier L k).observations.observations p) c lo ((carrier L k).terminal p))).range →
      let Z := (carrier L k).observations.observations p
      let hi := (carrier L k).terminal p
      let A := intervalCovariance Z c lo hi
      let B := intervalCovariance Z (fun r => R.reference r-c r) lo hi
      fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference Z lo hi)
        (UncutSmoothWords.test L k p)) z d=
        ∫ old,∫ residual,oldAverage L c k p (z+old+residual)*MeasurableGaussianScores.firstScore A d old
          ∂multivariateGaussian 0 (B+∑ j,covariances L Z (fun r => R.reference r-c r) k p j)
          ∂multivariateGaussian 0 A := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,hs,_,hphysical⟩ := hp
  intro lo hlo hgap d z hd
  let Z := (carrier L k).observations.observations p
  let hi := (carrier L k).terminal p
  let A := intervalCovariance Z c lo hi
  let B := intervalCovariance Z (fun r => R.reference r-c r) lo hi
  have hZ : ∀ i,(Z i).stop≤(Z i).target := RecursiveScoreSupport.carrier_ages L hages k p
  have hstop : ∀ i,hi≤(Z i).stop := (carrier L k).stops_after p
  have hcn (r : Domain) : 0≤c r ∧ c r≤R.upper :=
    ⟨hell.le.trans (hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have hrn (r : Domain) : 0≤R.reference r-c r ∧ R.reference r-c r≤R.upper :=
    ⟨sub_nonneg.mpr (hb r).2,(sub_le_self _ (hcn r).1).trans
      ((le_abs_self _).trans (R.reference_bound r))⟩
  have ho : A.PosSemidef := interval_posSemidef Z hZ c hc hcn lo hi
  have hr : B.PosSemidef := interval_posSemidef Z hZ _ (R.reference_measurable.sub hc) hrn lo hi
  have hsum := interval_add_profiles Z hZ c (fun r => R.reference r-c r) hc
    (R.reference_measurable.sub hc) R.upper_nonneg R.upper_nonneg
    (fun r => by rw [abs_of_nonneg (hcn r).1];exact (hcn r).2)
    (fun r => by rw [abs_of_nonneg (hrn r).1];exact (hrn r).2) lo hi
  have hsum' : intervalCovariance Z R.reference lo hi=A+B := by simpa only [add_sub_cancel] using hsum
  have he := PhysicalIntervalCovariance.interval_eq_covariance Z R.reference R.reference_measurable
    R.reference_bound hZ hstop hlo hgap.le
  have hfull : WordRecursion.covariance R.reference Z lo hi=A+B := he.symm.trans hsum'
  have h := chain.terminal_fderiv_reserved_score hs ho hr hd z
  have hid : (fun w => UncutSmoothWords.test L k p (projection (fun i : Fin (n+k) => i) w))=
      UncutSmoothWords.test L k p := rfl
  rw [hid] at h
  have havg : chain.oldAverage=oldAverage L c k p := by
    unfold Chain.oldAverage oldAverage
    rw [Physical.old_eq L Z c chain hphysical,Physical.direction_eq L Z c chain hphysical,fullTest_eq_word L chain]
  rw [Physical.residual_eq L Z c chain hphysical,havg] at h
  dsimp only
  rw [hfull]
  exact h

theorem terminal_range_assignments_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ lo : ℝ,0≤lo → lo<(carrier L k).terminal p →
      ∀ (d z : WordRecursion.State (n+k)),
      d∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance
        ((carrier L k).observations.observations p) c lo ((carrier L k).terminal p))).range →
      let Z := (carrier L k).observations.observations p
      let hi := (carrier L k).terminal p
      let A := intervalCovariance Z c lo hi
      let B := intervalCovariance Z (fun r => R.reference r-c r) lo hi
      fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference Z lo hi)
        (UncutSmoothWords.test L k p)) z d=
        ∫ terminal,∫ residual,((1/2:ℝ)^k*
          ∫ old,(∏ j,MeasurableGaussianScores.secondScore (covariances L Z c k p j)
            (directions L Z k p j) (old j))*assignedSum L k p z (terminal+residual) old
            ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k)) (covariances L Z c k p j)))*
          MeasurableGaussianScores.firstScore A d terminal
          ∂multivariateGaussian 0 (B+∑ j,covariances L Z (fun r => R.reference r-c r) k p j)
          ∂multivariateGaussian 0 A := by
  filter_upwards [terminal_range_first_score_ae L c hc hell hb hages μ k,
    oldAverage_assignment_ae L c hc hell hb hages μ k] with p hp ha
  intro lo hlo hgap d z hd
  dsimp only
  rw [hp lo hlo hgap d z hd]
  apply integral_congr_ae
  apply ae_of_all
  intro terminal
  apply integral_congr_ae
  apply ae_of_all
  intro residual
  dsimp only
  rw [show z+terminal+residual=z+(terminal+residual) by abel,ha z (terminal+residual)]

end SHE.PhysicalChainArrays
