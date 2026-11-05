module

public import SHE.CoveredTerminalFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace SHE.CoveredTerminalMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  PhysicalParentGeometry CoveredTerminalFactors MeasurableGaussianScores
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {n : ℕ}

def scoreScale {R : ReferenceData} (L : CutoffWordLevel.Level R X n) (c : Domain→ℝ)
    (k : ℕ) (p : History X k) (q : ℝ) (direction : WordRecursion.State (n+k)) : ℝ :=
  sqrt (scoreVariance (intervalCovariance ((carrier L k).observations.observations p) c q ((carrier L k).terminal p)) direction)*
    ∏ j,scoreVariance (covariances L ((carrier L k).observations.observations p) c k p j)
      (directions L ((carrier L k).observations.observations p) k p j)

variable (P : CanonicalCovariance.ProfileParameters)
variable (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

theorem scoreScale_eq (k : ℕ) (p : History X k) {q : ℝ} (hq0 : 0≤q)
    (hq : q≤(carrier L k).terminal p) (direction : WordRecursion.State (n+k)) :
    (∏ j : Fin (k+1),GaussianDependentScores.scale (flags j)
      (familyCovariance (stops L k p) (targets L k p) (centers L k p) (referenceProfile P Λ u dir)
        (lowerWith L k p q) (upperWith L k p) j)
      ((Fin.cons direction (directions L ((carrier L k).observations.observations p) k p) :
        Fin (k+1)→WordRecursion.State (n+k)) j))=
      scoreScale L (referenceProfile P Λ u dir) k p q direction := by
  rw [old_eq L _ k p hq0 hq]
  simp [Fin.prod_univ_succ,flags,GaussianDependentScores.scale,GaussianFreshFraction.covariances,scoreScale]

def boundScale (k : ℕ) (p : History X k) (q : ℝ) (direction mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1)))
    (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)) (A0 ν : ℝ) : ℝ :=
  scoreScale L (referenceProfile P Λ u dir) k p q direction*
    VectorPhysicalRoot.scale (liftChoices choices) 0 (lowerWith L k p q) (upperWith L k p) A0 ν (P.lower/2) n*
    ∏ j,WindowAssignedFactors.leafScale P (liftChoices choices) j.succ
      (lowerWith L k p q) (upperWith L k p) (targets L k p (leafIndex k (fun i => i) j))
      (mean (leafIndex k (fun i => i) j))
      (ControlledProfile.mean Λ u dir
        (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))) (chosen j)

/-- Actual terminal assigned words of the original recursive controlled
level have every fixed even Gaussian moment, with exact first-score
degree, all old second-score energies and clips, and honest displaced
current means. All interval, native-baseline, covariance and range
applicability is discharged from the literal history construction. -/
theorem even_moment_ae
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) μ k,
      ∀ q : ℝ,0≤q → q<(carrier L k).terminal p → StrictHistory L k p →
      ∀ direction mean : WordRecursion.State (n+k),
      direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance ((carrier L k).observations.observations p)
        (referenceProfile P Λ u dir) q ((carrier L k).terminal p))).range →
      ∀ (choices : List (Fin k×Fin (k+1))), (choices.map Prod.fst).Nodup →
      ∀ (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)),
      (∀ j h,chosen j h∈block (liftChoices choices) j.succ) →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      ContDiff ℝ (block (liftChoices choices) 0).length (L.test (rootParameter k p)) →
      (∀ j,j≤(block (liftChoices choices) 0).length → ∀ z,
        ‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b →
      Integrable (fun x => |assignedWord P ha Λ u dir θ L k p q direction mean choices x|^(2*b))
        (terminalAssignedMeasure L (referenceProfile P Λ u dir) k p q) ∧
      (∫ x,|assignedWord P ha Λ u dir θ L k p q direction mean choices x|^(2*b)
        ∂terminalAssignedMeasure L (referenceProfile P Λ u dir) k p q)≤
      WindowFirstScoreMoments.constant P (k+1) k (liftChoices choices) b*
        (boundScale P ha Λ u dir θ L k p q direction mean choices chosen A0 ν)^(2*b) := by
  have hb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [exists_chain_ae L _ (referenceProfile_measurable P Λ u dir)
    (mul_pos (fraction_pos P) P.lower_pos) hb hages μ k,
    measure_eq_ae P ha Λ u dir θ L hages μ k] with p hp hmeasure
  obtain ⟨chain,_,_,hphysical⟩ := hp
  intro q hq0 hq hp direction mean hd choices hnd chosen hchosen A0 ν hA0 hν hf hfb b hb0
  have hage (i : Fin (n+k)) : stops L k p i≤targets L k p i :=
    (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages L hages k p i)
  have hD (j : Fin (k+1)) :
      (Fin.cons direction (directions L ((carrier L k).observations.observations p) k p) :
        Fin (k+1)→WordRecursion.State (n+k)) j∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (familyCovariance (stops L k p) (targets L k p) (centers L k p)
        (referenceProfile P Λ u dir) (lowerWith L k p q) (upperWith L k p) j)).range := by
    rw [old_eq L _ k p hq0 hq.le]
    refine Fin.cases hd (fun j => ?_) j
    rw [←Physical.old_eq L _ _ chain hphysical,←Physical.direction_eq L _ _ chain hphysical]
    exact chain.assigned_direction_mem_range j
  have hh := WindowFirstScoreMoments.even_moment P Λ u dir θ
    (lowerWith L k p q) (upperWith L k p) (disjointWith L k p q)
    (stops L k p) (targets L k p) (centers L k p)
    (stops_pos P ha Λ u dir θ L k p hq0 hq) (stops_le_one P ha Λ u dir θ L k p) hage
    hq0 (lowerWith_bound L k p hq.le) (gapWith L k p hp hq) (stopWith L k p q)
    flags (Fin.cons direction (directions L ((carrier L k).observations.observations p) k p)) hD mean
    (rootSelector k (fun i => i)) (leafIndex k (fun i => i))
    (leaf_native P ha Λ u dir θ L k p hp) (leaf_time P ha Λ u dir θ L k p hp hq0 hq)
    (liftChoices choices) (lift_nodup choices hnd) chosen hchosen
    (L.test (rootParameter k p)) (L.test_uniform.smooth _).continuous.measurable hA0 hν hf hfb b hb0
  dsimp only at hh
  rw [scoreScale_eq P ha Λ u dir θ L k p hq0 hq.le direction] at hh
  rw [hmeasure q hq0 hq.le]
  rw [assignedWord_eq P ha Λ u dir θ L k p hq0 hq.le direction mean choices]
  exact hh

end SHE.CoveredTerminalMoments
