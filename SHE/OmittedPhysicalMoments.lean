module

public import SHE.OmittedAssignedAverage
public import SHE.OmittedTimeFactor
public import SHE.PhysicalFullResidualAssignments
public import SHE.CoveredOldResidualCovariance
public import SHE.OldOnlyTimeFactor
public import SHE.CoveredTerminalMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.OmittedPhysicalMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  PhysicalChainArrays OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord ControlledOldIntervals MeasurableGaussianScores
open scoped BigOperators NNReal
local instance omittedPhysicalMoments_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) (ha : SmoothCylinders.BoundedSmooth P.coefficient)
variable (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
variable (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)

def value (k : ℕ) (p : History X k) (mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) (j0 : Fin k)
    (x : (Fin k→WordRecursion.State (n+k))×WordRecursion.State (n+k)) : ℝ :=
  OmittedAssignedMoments.oldScores
    (covariances L ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) k p)
    (directions L ((carrier L k).observations.observations p) k p) x*
      VectorControlledRoot.value choices 0 (L.test (rootParameter k p)) mean (rootSelector k (fun i=>i)) x*
        ∏ j∈Finset.univ.erase j0,ControlledAssignedLeaf.leaf choices j.succ
          (ControlledWordLevel.referenceData P ha Λ u dir θ).totalVariance mean
          (leafIndex k (fun i=>i) j) (baseline L k p j) x

/-- Genuine old-only erased-baseline assigned moments on the full actual
remaining Gaussian. Every original old score and root clip survives. -/
theorem assignment_even_moment_ae
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure (ControlledWordLevel.referenceData P ha Λ u dir θ) ρ k,
      ∀ q : ℝ≥0,(q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ mean : Ω→WordRecursion.State (n+k),Measurable mean →
      ∀ (choices : List (Fin k×Fin (k+1))), (choices.map Prod.fst).Nodup → ∀ j0 : Fin k,
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      ContDiff ℝ (block choices 0).length (L.test (rootParameter k p)) →
      (∀ j,j≤(block choices 0).length → ∀ z,
        ‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ b : ℕ,0<b → ∀ C0 : ℝ,0≤C0 →
      (∀ j : Fin k,j≠j0 → Integrable (fun ω => |mean ω (leafIndex k (fun i=>i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent)) μ ∧
        (∫ ω,|mean ω (leafIndex k (fun i=>i) j)-ControlledProfile.mean Λ u dir
          (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j)))|^
          (((2*(b*(k+2)):ℕ):ℝ)*P.exponent) ∂μ)≤
          C0*(targets L k p (leafIndex k (fun i=>i) j))^((b*(k+2):ℕ)*P.exponent/2)) →
      let W := fun ω=>∫ x,value P ha Λ u dir θ L k p (mean ω) choices j0 x
        ∂fullAssignedMeasure L (referenceProfile P Λ u dir) k p q
      Integrable (fun ω=>|W ω|^(2*b)) μ ∧ (∫ ω,|W ω|^(2*b) ∂μ)≤
        OmittedAssignedMoments.constant P k k choices j0 b C0*
          (scoreProduct L ((carrier L k).observations.observations p) (referenceProfile P Λ u dir) k p*
            OmittedTimeFactor.factor L P k p choices j0 A0 ν)^(2*b) := by
  have hcb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u dir r ∧
      referenceProfile P Λ u dir r≤(ControlledWordLevel.referenceData P ha Λ u dir θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u dir r).1,
      (referenceProfile_bounds P Λ u dir r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u dir (θ,r)).1)⟩
  filter_upwards [exists_chain_ae L _ (referenceProfile_measurable P Λ u dir)
    (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k,
    full_residual_eq_fixedReserve_ae P ha Λ u dir θ L hages ρ k] with p hp hresidual
  obtain ⟨chain,_,_,hphysical⟩ := hp
  intro q hq hp mean hm choices hnd j0 A0 ν hA0 hν hf hfb b hb0 C0 hC0 hoffset
  let Z := (carrier L k).observations.observations p
  have hZ := RecursiveScoreSupport.carrier_ages L hages k p
  have hage (i : Fin (n+k)) : stops L k p i≤targets L k p i := (min_le_left _ _).trans (hZ i)
  have hmatrix := CoveredControlledLaw.old_family_eq L (referenceProfile P Λ u dir) k p q.2 hq.le
  have hres := hresidual q q.2 hq.le
  have hD (j : Fin k) : directions L Z k p j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance (stops L k p) (targets L k p) (centers L k p)
        (referenceProfile P Λ u dir) (lower L k p) (upper L k p) j)).range := by
    rw [hmatrix,←Physical.old_eq L Z _ chain hphysical,←Physical.direction_eq L Z _ chain hphysical]
    exact chain.assigned_direction_mem_range j
  have hh := OmittedAssignedMoments.averaged_even_moment μ P Λ u dir θ q q.2
    (stops L k p) (targets L k p) (centers L k p)
    (stops_pos P ha Λ u dir θ L k p q.2 hq) (stops_le_one P ha Λ u dir θ L k p) hage
    (lower L k p) (upper L k p) (fun j=>hq.le.trans (terminal_le_lower L k p j))
    (lower_lt_upper L k p hp) (fun j i=>by
      rcases stop_dichotomy L k p j i with h|h
      · exact Or.inl ((min_le_left _ _).trans h)
      · exact Or.inr (le_min h (upper_le_initial L k p j)))
    (disjoint L k p) mean hm (directions L Z k p) hD
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i))
    (leaf_native P ha Λ u dir θ L k p hp) (leaf_time P ha Λ u dir θ L k p hp q.2 hq)
    choices hnd j0 (OldOnlyTimeFactor.chosen L k p choices) (OldOnlyTimeFactor.chosen_mem L k p choices)
    (L.test (rootParameter k p)) (L.test_uniform.smooth _).continuous.measurable
    hA0 hν hf hfb b hb0 C0 hC0 hoffset
  dsimp only at hh
  erw [hmatrix,←hres] at hh
  have hbase : (fun j=>ControlledProfile.profile P Λ u dir
      (θ,(targets L k p (leafIndex k (fun i=>i) j),centers L k p (leafIndex k (fun i=>i) j))))=
      baseline L k p := funext (fun j=>(CoveredTerminalFactors.baseline_eq P ha Λ u dir θ L k p j).symm)
  erw [hbase] at hh
  dsimp only [ControlledWordLevel.referenceData,Z] at hh ⊢
  simpa only [value,scoreProduct,fullAssignedMeasure,OmittedAssignedMoments.word,
    OmittedTimeFactor.factor,ControlledWordLevel.referenceData,mul_assoc] using hh

end SHE.OmittedPhysicalMoments
