module

public import SHE.PhysicalTerminalNorm
public import SHE.StoppedWindowCovariance
public import SHE.ControlledWindowDecomposition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.CoveredControlledCovariance
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n N : ℕ}

/-- Clipping at the covered initial horizon changes no earlier actual
interval covariance; every original target and center is retained. -/
theorem interval_clip_upper (Z : Fin N→Observation) (c : Domain→ℝ)
    {lo hi H : ℝ} (hlo : 0≤lo) (hhi : hi≤H) :
    intervalCovariance (StoppedWindowCovariance.clipped Z H) c lo hi=intervalCovariance Z c lo hi := by
  rw [StoppedWindowCovariance.interval_eq_clipped _ _ hlo,
    StoppedWindowCovariance.interval_eq_clipped _ _ hlo]
  congr 2
  funext i
  change min (min (Z i).stop H) hi=min (Z i).stop hi
  rw [min_assoc,min_eq_right hhi]

/-- Exact total covariance in the fresh-plus-old terminal score
representation. The window ends at the initial terminal time, even when
the original root targets or stops lie later. -/
theorem terminal_decomposition_ae (L : CutoffWordLevel.Level R X n)
    (c : Domain→ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0<ell)
    (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ lo : ℝ,0≤lo → lo≤(carrier L k).terminal p →
      let Z := (carrier L k).observations.observations p
      let T := (carrier L k).terminal p
      (∑ j,GaussianFreshFraction.covariances (intervalCovariance Z c lo T)
        (covariances L Z c k p) j)+
        (intervalCovariance Z (fun r => R.reference r-c r) lo T+
          ∑ j,covariances L Z (fun r => R.reference r-c r) k p j)=
        stoppedCovariance (fun i => min (Z i).stop (initialTerminal L k p))
          (fun i => (Z i).target) (fun i => (Z i).center) R.reference lo := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,_,_,hphysical⟩ := hp
  intro lo hlo hgap
  let Z := (carrier L k).observations.observations p
  let T := (carrier L k).terminal p
  have hZ : ∀ i,(Z i).stop≤(Z i).target := RecursiveScoreSupport.carrier_ages L hages k p
  have hc0 (r : Domain) : 0≤c r ∧ c r≤R.upper :=
    ⟨hell.le.trans (hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have hr0 (r : Domain) : 0≤R.reference r-c r ∧ R.reference r-c r≤R.upper :=
    ⟨sub_nonneg.mpr (hb r).2,(sub_le_self _ (hc0 r).1).trans
      ((le_abs_self _).trans (R.reference_bound r))⟩
  have hs := Physical.sum_full L Z hZ c hc hell hb chain hphysical
  rw [Physical.old_eq L Z c chain hphysical,Physical.residual_eq L Z c chain hphysical] at hs
  have hf := interval_add_profiles Z hZ c (fun r => R.reference r-c r) hc (R.reference_measurable.sub hc)
    R.upper_nonneg R.upper_nonneg
    (fun r => by rw [abs_of_nonneg (hc0 r).1];exact (hc0 r).2)
    (fun r => by rw [abs_of_nonneg (hr0 r).1];exact (hr0 r).2) lo T
  have hf' : intervalCovariance Z c lo T+intervalCovariance Z (fun r => R.reference r-c r) lo T=
      intervalCovariance Z R.reference lo T := by simpa only [add_sub_cancel] using hf.symm
  dsimp only
  rw [Fin.sum_univ_succ]
  change intervalCovariance Z c lo T+(∑ j,covariances L Z c k p j)+
    (intervalCovariance Z (fun r => R.reference r-c r) lo T+
      ∑ j,covariances L Z (fun r => R.reference r-c r) k p j)=_
  calc
    _ = (intervalCovariance Z c lo T+intervalCovariance Z (fun r => R.reference r-c r) lo T)+
        ∑ j,(covariances L Z c k p j+covariances L Z (fun r => R.reference r-c r) k p j) := by
          rw [Finset.sum_add_distrib]
          abel
    _ = intervalCovariance Z R.reference lo T+
        intervalCovariance Z R.reference T (initialTerminal L k p) := by rw [hf',hs]
    _ = intervalCovariance Z R.reference lo (initialTerminal L k p) :=
      interval_add_adjacent Z hZ R.reference R.reference_measurable R.upper_nonneg R.reference_bound
        hgap (terminal_le_initial L k p)
    _ = _ := StoppedWindowCovariance.interval_eq_clipped Z R.reference hlo

end SHE.CoveredControlledCovariance
