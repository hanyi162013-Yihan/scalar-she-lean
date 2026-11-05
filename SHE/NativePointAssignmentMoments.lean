module

public import SHE.NativePhysicalWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section

namespace SHE.NativePointAssignmentMoments
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  NativeObservationNaturality PhysicalProfile PhysicalMeanSemigroup ControlledFutureMeans
  StoppedGaussianFeatures StoppedGaussianScore FiniteHaar StoppedFourier OrthogonalItoChannels
  DyadicApproximation GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  GaussianCoordinates ProjectedUncutWord PhysicalScoreChain PhysicalChainArrays GaussianConvolution
  GaussianFreshAssignments ProfileL2 CoveredHistoryGeometry CoveredControlledLaw PhysicalParentGeometry
  CoveredTerminalFactors CoveredTerminalMoments NativePhysicalWord
open scoped NNReal ENNReal BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) X n)

def actualMean (k : ℕ) (q : ℝ≥0) (ω : Ω) (p : History X k) : WordRecursion.State (n+k) :=
  ActualMeanKernel.controlledMean L k Λ q q.2 (embed u₀) (embed (v₀-u₀))
    (fun ω => embed (S.first q ω)) (fun ω => embed (S.second q ω-S.first q ω)) θ ω p

def boundScale (k : ℕ) (p : History X k) (q : ℝ) (y : HeatCircle)
    (choices : List (Fin k×Fin (k+1)))
    (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)) (A0 ν : ℝ) : ℝ :=
  scoreScale L (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) k p q
      (heatRow ((carrier L k).observations.observations p) q y)*
    VectorPhysicalRoot.scale (liftChoices choices) 0 (lowerWith L k p q) (upperWith L k p) A0 ν (P.lower/2) n*
    ∏ j,NativeAssignedLeafMoments.leafScale P (liftChoices choices) j.succ
      (lowerWith L k p q) (upperWith L k p) (targets L k p (leafIndex k (fun i => i) j)) (chosen j)

include hIJ₀ hIJ₁ in
/-- The literal assigned point kernel at the actual constructed native
current state has every fixed moment at its deterministic physical
scale. Native masks, original targets/centers, all old root clips,
assigned rough gaps and unassigned full ages are preserved. -/
theorem assignment_even_moment_ae (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) ρ k,
      ∀ q : ℝ≥0,q≤H → (q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
      ∀ (choices : List (Fin k×Fin (k+1))), (choices.map Prod.fst).Nodup →
      ∀ (chosen : ∀ j : Fin k,block (liftChoices choices) j.succ≠[]→Fin (k+1)),
      (∀ j h,chosen j h∈block (liftChoices choices) j.succ) →
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      ContDiff ℝ (block (liftChoices choices) 0).length (L.test (rootParameter k p)) →
      (∀ j,j≤(block (liftChoices choices) 0).length → ∀ z,
        ‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ (b : ℕ),0<b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
      let νG := terminalAssignedMeasure L (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) k p q
      let W := fun ω => ∫ x,rangeAssignedWord L (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) k p q
        (heatRow ((carrier L k).observations.observations p) q y)
        (actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP θ L k q ω p) choices x ∂νG
      Integrable (fun ω => |W ω|^(2*b)) μ ∧ (∫ ω,|W ω|^(2*b) ∂μ)≤
        NativeFirstScoreWordMoments.constant P (k+1) k (liftChoices choices) b B0 κ M*
          (boundScale Λ u₀ v₀ P haP θ L k p q y choices chosen A0 ν)^(2*b) := by
  let u := embed u₀
  let d0 := embed (v₀-u₀)
  have hcb (r : Domain) : fraction P*P.lower≤referenceProfile P Λ u d0 r ∧
      referenceProfile P Λ u d0 r≤(ControlledWordLevel.referenceData P haP Λ u d0 θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u d0 r).1,
      (referenceProfile_bounds P Λ u d0 r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u d0 (θ,r)).1)⟩
  filter_upwards [exists_chain_ae L _ (referenceProfile_measurable P Λ u d0)
    (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k,
    measure_eq_ae P haP Λ u d0 θ L hages ρ k] with p hp hmeasure
  obtain ⟨chain,_,_,hphysical⟩ := hp
  intro q hqH hq hp
  have hq1 : (q:ℝ)≤1 := hq.le.trans (((carrier L k).terminal_horizon p).trans P.horizon_le_one)
  have hZ := RecursiveScoreSupport.carrier_ages L hages k p
  filter_upwards [PhysicalFirstScore.terminal_heatRow_mem_range_ae
    ((carrier L k).observations.observations p) q.2 hq
    (((carrier L k).terminal_horizon p).trans P.horizon_le_one) ((carrier L k).stops_after p) hZ
    (referenceProfile P Λ u d0) (referenceProfile_measurable P Λ u d0)
    (mul_pos (fraction_pos P) P.lower_pos) (referenceProfile_bounds P Λ u d0)] with y hy
  intro choices hnd chosen hchosen A0 ν hA0 hν hf hfb b hb0 B0 hBDG
  let row := heatRow ((carrier L k).observations.observations p) q y
  have hage (i : Fin (n+k)) : stops L k p i≤targets L k p i := (min_le_left _ _).trans (hZ i)
  have hD (j : Fin (k+1)) :
      (Fin.cons row (directions L ((carrier L k).observations.observations p) k p) :
        Fin (k+1)→WordRecursion.State (n+k)) j∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (familyCovariance (stops L k p) (targets L k p)
        (nativeCenter (unitCenters L k p)) (referenceProfile P Λ u d0)
        (lowerWith L k p q) (upperWith L k p) j)).range := by
    have he : familyCovariance (stops L k p) (targets L k p) (nativeCenter (unitCenters L k p))
        (referenceProfile P Λ u d0) (lowerWith L k p q) (upperWith L k p)=
        GaussianFreshFraction.covariances
          (intervalCovariance ((carrier L k).observations.observations p) (referenceProfile P Λ u d0) q ((carrier L k).terminal p))
          (covariances L ((carrier L k).observations.observations p) (referenceProfile P Λ u d0) k p) := by
      rw [native_centers L k p]
      exact CoveredControlledLaw.old_eq L _ k p q.2 hq.le
    have hx (j : Fin (k+1)) :
        (Fin.cons row (directions L ((carrier L k).observations.observations p) k p) :
          Fin (k+1)→WordRecursion.State (n+k)) j∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (GaussianFreshFraction.covariances
          (intervalCovariance ((carrier L k).observations.observations p) (referenceProfile P Λ u d0) q ((carrier L k).terminal p))
          (covariances L ((carrier L k).observations.observations p) (referenceProfile P Λ u d0) k p) j)).range := by
      refine Fin.cases hy (fun j => ?_) j
      rw [←Physical.old_eq L _ _ chain hphysical,←Physical.direction_eq L _ _ chain hphysical]
      exact chain.assigned_direction_mem_range j
    exact (congrArg (fun A => (Fin.cons row (directions L ((carrier L k).observations.observations p) k p) :
      Fin (k+1)→WordRecursion.State (n+k)) j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range) (congrFun he j)).mpr (hx j)
  have hh := NativeFirstScoreWordMoments.averaged_even_moment 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ P hΛ q hqH hq1 (stops L k p) (targets L k p) (unitCenters L k p)
    (stops_pos P haP Λ u d0 θ L k p q.2 hq) (stops_le_one P haP Λ u d0 θ L k p) hage
    (carrier_targets_after L p hages hq)
    (lowerWith L k p q) (upperWith L k p) (lowerWith_bound L k p hq.le)
    (gapWith L k p hp hq) (stopWith L k p q) (disjointWith L k p q) hθ flags
    (Fin.cons row (directions L ((carrier L k).observations.observations p) k p)) hD
    (rootSelector k (fun i => i)) (leafIndex k (fun i => i))
    (leaf_native P haP Λ u d0 θ L k p hp) (leaf_time P haP Λ u d0 θ L k p hp q.2 hq)
    (liftChoices choices) (lift_nodup choices hnd) chosen hchosen
    (L.test (rootParameter k p)) (L.test_uniform.smooth _).continuous.measurable hA0 hν hf hfb b hb0 B0 hBDG
  dsimp only at hh
  rw [native_centers L k p] at hh
  have hmatrix := CoveredControlledLaw.old_eq L
    (referenceProfile P Λ (embed u₀) (embed (v₀-u₀))) k p q.2 hq.le
  erw [hmatrix] at hh
  have hbase : (fun j => ControlledProfile.profile P Λ (embed u₀) (embed (v₀-u₀))
      (θ,(targets L k p (leafIndex k (fun i => i) j),centers L k p (leafIndex k (fun i => i) j))))=
      baseline L k p := funext (fun j => (CoveredTerminalFactors.baseline_eq P haP Λ (embed u₀)
        (embed (v₀-u₀)) θ L k p j).symm)
  erw [hbase] at hh
  rw [hmeasure q q.2 hq.le]
  dsimp only
  erw [hmatrix]
  simp only [Fin.prod_univ_succ,flags,GaussianFreshFraction.covariances,Fin.cases_zero,Fin.cases_succ,
    Fin.cons_zero,Fin.cons_succ,GaussianDependentScores.scale,Bool.false_eq_true,ite_false,ite_true] at hh
  convert! hh using 1

end SHE.NativePointAssignmentMoments
