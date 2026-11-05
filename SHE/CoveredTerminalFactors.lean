module

public import SHE.PhysicalPointRowRange
public import SHE.WindowFirstScoreMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2900000
noncomputable section

namespace SHE.CoveredTerminalFactors
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals PhysicalParentGeometry
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {n : ℕ}

theorem lift_nodup {r m : ℕ} (choices : List (Fin r×Fin m)) (hnd : (choices.map Prod.fst).Nodup) :
    ((liftChoices choices).map Prod.fst).Nodup := by
  have he : (liftChoices choices).map Prod.fst=(choices.map Prod.fst).map Fin.succ := by
    simp only [liftChoices,List.map_map,Function.comp_def]
  rw [he]
  exact hnd.map (Fin.succ_injective _)

variable (P : CanonicalCovariance.ProfileParameters)
variable (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

theorem stops_pos (k : ℕ) (p : History X k) {q : ℝ} (hq0 : 0≤q) (hq : q<(carrier L k).terminal p)
    (i : Fin (n+k)) : 0<stops L k p i :=
  (hq0.trans_lt hq).trans_le (le_min ((carrier L k).stops_after p i) (terminal_le_initial L k p))

theorem stops_le_one (k : ℕ) (p : History X k) (i : Fin (n+k)) : stops L k p i≤1 :=
  (min_le_right _ _).trans ((L.terminal_horizon (rootParameter k p)).trans P.horizon_le_one)

theorem leaf_native (k : ℕ) (p : History X k) (hp : StrictHistory L k p) (j : Fin k) :
    stops L k p (leafIndex k (fun i => i) j)=targets L k p (leafIndex k (fun i => i) j) := by
  unfold stops targets
  rw [leaf_observation L k p j]
  exact min_eq_left ((lower_lt_upper L k p hp j).le.trans (upper_le_initial L k p j))

theorem leaf_time (k : ℕ) (p : History X k) (hp : StrictHistory L k p)
    {q : ℝ} (hq0 : 0≤q) (hq : q<(carrier L k).terminal p) (j : Fin k) :
    targets L k p (leafIndex k (fun i => i) j)∈Ioc 0 P.horizon := by
  unfold targets
  rw [leaf_observation L k p j]
  exact ⟨(hq0.trans_lt hq).trans_le (terminal_le_lower L k p j),
    ((lower_lt_upper L k p hp j).le.trans (upper_le_initial L k p j)).trans
      (L.terminal_horizon (rootParameter k p))⟩

theorem baseline_eq (k : ℕ) (p : History X k) (j : Fin k) :
    baseline L k p j=ControlledProfile.profile P Λ u dir
      (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j))) := by
  unfold targets centers
  rw [leaf_observation L k p j]
  rfl

def assignedWord (k : ℕ) (p : History X k) (q : ℝ) (direction mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) :
    ((Fin (k+1)→WordRecursion.State (n+k))×WordRecursion.State (n+k))→ℝ :=
  let Z := (carrier L k).observations.observations p
  WindowFirstScoreWord.word P.coefficient flags
    (GaussianFreshFraction.covariances (intervalCovariance Z (referenceProfile P Λ u dir) q ((carrier L k).terminal p))
      (covariances L Z (referenceProfile P Λ u dir) k p))
    (Fin.cons direction (directions L Z k p)) (liftChoices choices)
    (L.test (rootParameter k p)) mean (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p)

theorem assignedWord_eq (k : ℕ) (p : History X k) {q : ℝ} (hq0 : 0≤q)
    (hq : q≤(carrier L k).terminal p) (direction mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) :
    assignedWord P ha Λ u dir θ L k p q direction mean choices=
      WindowFirstScoreMoments.word P.coefficient flags
        (familyCovariance (stops L k p) (targets L k p) (centers L k p)
          (referenceProfile P Λ u dir) (lowerWith L k p q) (upperWith L k p))
        (Fin.cons direction (directions L ((carrier L k).observations.observations p) k p))
        (liftChoices choices) (L.test (rootParameter k p)) mean
        (rootSelector k (fun i => i)) (leafIndex k (fun i => i))
        (fun j => ControlledProfile.profile P Λ u dir
          (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))) := by
  unfold assignedWord
  dsimp only
  rw [←old_eq L _ k p hq0 hq]
  have hb : baseline L k p=(fun j => ControlledProfile.profile P Λ u dir
      (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))) :=
    funext (baseline_eq P ha Λ u dir θ L k p)
  rw [hb]
  rfl

end SHE.CoveredTerminalFactors
