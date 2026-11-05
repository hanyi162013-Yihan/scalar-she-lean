module

public import SHE.OffsetFirstScoreWordMoments
public import SHE.PhysicalWordTimeScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.PhysicalOffsetPointAssignments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord ControlledOldIntervals
open scoped BigOperators NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

/-- The actual physical assigned point word, with an arbitrary current
mean and arbitrary genuine q-covariance-range direction. The only
current-state input is its scalar leaf displacement moment; all Gaussian
score, root, rough block, baseline and physical range identifications are
proved. This allows the joint stopped flow as well as compensated means. -/
theorem assignment_even_moment_ae
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) ρ k,
      ∀ q : ℝ≥0,(q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ direction : WordRecursion.State (n+k),direction∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (intervalCovariance ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) q ((carrier L k).terminal p))).range →
      ∀ mean : Ω→WordRecursion.State (n+k),Measurable mean →
      ∀ (choices : List (Fin k×Fin (k+1))), (choices.map Prod.fst).Nodup →
      ∀ (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)),
      (∀ j h,chosen j h∈block (liftChoices choices) j.succ) →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      ContDiff ℝ (block (liftChoices choices) 0).length (L.test (rootParameter k p)) →
      (∀ j,j≤(block (liftChoices choices) 0).length → ∀ z,
        ‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ C0 : ℝ,0≤C0 →
      (∀ j : Fin k,Integrable (fun ω => |mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent)) μ ∧
        (∫ ω,|mean ω (leafIndex k (fun i => i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
          C0*(targets L k p (leafIndex k (fun i => i) j))^((b*(k+2):ℕ)*P.exponent/2)) →
      let νG := terminalAssignedMeasure L (referenceProfile P Λ u dir) k p q
      let W := fun ω => ∫ x,rangeAssignedWord L (referenceProfile P Λ u dir) k p q direction (mean ω) choices x ∂νG
      Integrable (fun ω => |W ω|^(2*b)) μ ∧ (∫ ω,|W ω|^(2*b) ∂μ)≤
        OffsetFirstScoreWordMoments.constant P (k+1) k (liftChoices choices) b C0*
          (scoreScale L (referenceProfile P Λ u dir) k p q direction*
            PhysicalWordTimeScale.factor L P k p q choices chosen A0 ν)^(2*b) := by
  have hcb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [exists_chain_ae L _ (referenceProfile_measurable P Λ u dir)
    (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k,
    measure_eq_ae P ha Λ u dir θ L hages ρ k] with p hp hmeasure
  obtain ⟨chain,_,_,hphysical⟩ := hp
  intro q hq hp row hy mean hm choices hnd chosen hchosen A0 ν hA0 hν hf hfb b hb0 C0 hC0 hoffset
  have hZ := RecursiveScoreSupport.carrier_ages L hages k p
  have hage (i : Fin (n+k)) : stops L k p i≤targets L k p i := (min_le_left _ _).trans (hZ i)
  have hD (j : Fin (k+1)) :
      (Fin.cons row (directions L ((carrier L k).observations.observations p) k p) :
        Fin (k+1)→WordRecursion.State (n+k)) j∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (familyCovariance (stops L k p) (targets L k p)
        (centers L k p) (referenceProfile P Λ u dir) (lowerWith L k p q) (upperWith L k p) j)).range := by
    have he := CoveredControlledLaw.old_eq L (referenceProfile P Λ u dir) k p q.2 hq.le
    have hx (j : Fin (k+1)) :
        (Fin.cons row (directions L ((carrier L k).observations.observations p) k p) :
          Fin (k+1)→WordRecursion.State (n+k)) j∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (GaussianFreshFraction.covariances
          (intervalCovariance ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) q ((carrier L k).terminal p))
          (covariances L ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) k p) j)).range := by
      refine Fin.cases hy (fun j => ?_) j
      rw [←Physical.old_eq L _ _ chain hphysical,←Physical.direction_eq L _ _ chain hphysical]
      exact chain.assigned_direction_mem_range j
    exact (congrArg (fun A => (Fin.cons row (directions L ((carrier L k).observations.observations p) k p) :
      Fin (k+1)→WordRecursion.State (n+k)) j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) (congrFun he j)).mpr (hx j)
  have hh := OffsetFirstScoreWordMoments.averaged_even_moment μ P Λ u dir θ q q.2
    (stops L k p) (targets L k p) (centers L k p)
    (stops_pos P ha Λ u dir θ L k p q.2 hq) (stops_le_one P ha Λ u dir θ L k p) hage
    (lowerWith L k p q) (upperWith L k p) (lowerWith_bound L k p hq.le)
    (gapWith L k p hp hq) (stopWith L k p q) (disjointWith L k p q) mean hm flags
    (Fin.cons row (directions L ((carrier L k).observations.observations p) k p)) hD
    (rootSelector k (fun i => i)) (leafIndex k (fun i => i))
    (leaf_native P ha Λ u dir θ L k p hp) (leaf_time P ha Λ u dir θ L k p hp q.2 hq)
    (liftChoices choices) (lift_nodup choices hnd) chosen hchosen
    (L.test (rootParameter k p)) (L.test_uniform.smooth _).continuous.measurable hA0 hν hf hfb b hb0 C0 hC0 hoffset
  dsimp only at hh
  have hmatrix := CoveredControlledLaw.old_eq L (referenceProfile P Λ u dir) k p q.2 hq.le
  erw [hmatrix] at hh
  have hbase : (fun j => ControlledProfile.profile P Λ u dir
      (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j))))=
      baseline L k p := funext (fun j => (CoveredTerminalFactors.baseline_eq P ha Λ u dir θ L k p j).symm)
  erw [hbase] at hh
  rw [hmeasure q q.2 hq.le]
  dsimp only
  erw [hmatrix]
  simp only [Fin.prod_univ_succ,flags,GaussianFreshFraction.covariances,Fin.cases_zero,Fin.cases_succ,
    Fin.cons_zero,Fin.cons_succ,GaussianDependentScores.scale,Bool.false_eq_true,ite_false,ite_true] at hh
  simp only [PhysicalWordTimeScale.factor,scoreScale,mul_assoc] at hh ⊢
  convert! hh using 1

end SHE.PhysicalOffsetPointAssignments
