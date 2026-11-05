module

public import SHE.ActualPointMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace SHE.NativeActualPointMoments
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

def assignmentConstant (k : ℕ) (p : History X k) (q : ℝ) (y : HeatCircle)
    (b : ℕ) (B0 : ℝ≥0) (A0 ν : ℝ) (choices : List (Fin k×Fin (k+1))) : ℝ :=
  NativeFirstScoreWordMoments.constant P (k+1) k (liftChoices choices) b B0 κ M*
    (NativePointAssignmentMoments.boundScale Λ u₀ v₀ P haP θ L k p q y choices
      (ActualPointMomentSum.chosen choices) A0 ν)^(2*b)

include hIJ₀ hIJ₁ in
/-- Every fixed even moment of the literal physical current-mean point
kernel, at the actual native pair state. The finite assignment sum
retains its individual old root clips, selected rough gaps and the
terminal point-row score; no normalized-kernel premise is assumed. -/
theorem point_even_moment_ae (hΛ : 0≤Λ) (hθ : |θ|≤1)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure
      (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) ρ k,
      ∀ q : ℝ≥0,q≤H → (q:ℝ)<(carrier L k).terminal p → StrictHistory L k p →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
      ∀ A0 ν : ℝ,0≤A0 → 0≤ν →
      (∀ j,j≤k → ∀ z,‖iteratedFDeriv ℝ j (L.test (rootParameter k p)) z‖≤A0*ν^j) →
      ∀ (b : ℕ),0<b → ∀ B0 : ℝ≥0,StandardTerminalBDGPower (b*(k+2)) J B0 →
      let F := fun ω => ActualMeanKernel.point L k q
        (NativePointAssignmentMoments.actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP θ L k q ω) p y
      let cs := assignments (m:=k+1) (List.finRange k)
      Integrable (fun ω => |F ω|^(2*b)) μ ∧ (∫ ω,|F ω|^(2*b) ∂μ)≤
        ((1/2:ℝ)^k)^(2*b)*(cs.length:ℝ)^(2*b-1)*
          (cs.map (assignmentConstant (M:=M) Λ κ u₀ v₀ P haP θ L k p q y b B0 A0 ν)).sum := by
  let u := embed u₀
  let d0 := embed (v₀-u₀)
  let c := referenceProfile P Λ u d0
  have hcb (r : Domain) : fraction P*P.lower≤c r ∧
      c r≤(ControlledWordLevel.referenceData P haP Λ u d0 θ).reference r :=
    ⟨(referenceProfile_bounds P Λ u d0 r).1,
      (referenceProfile_bounds P Λ u d0 r).2.trans ((half_le_self P.lower_pos.le).trans
        (ControlledProfile.profile_bounds P Λ u d0 (θ,r)).1)⟩
  filter_upwards [NativePointAssignmentMoments.assignment_even_moment_ae
    𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ P haP θ L hΛ hθ hages ρ k,
    terminal_range_integral_ae L c (referenceProfile_measurable P Λ u d0)
      (mul_pos (fraction_pos P) P.lower_pos) hcb hages ρ k] with p hmoment hrepresentation
  intro q hqH hq hp
  have hZ := RecursiveScoreSupport.carrier_ages L hages k p
  filter_upwards [hmoment q hqH hq hp,
    PhysicalFirstScore.terminal_heatRow_mem_range_ae
      ((carrier L k).observations.observations p) q.2 hq
      (((carrier L k).terminal_horizon p).trans P.horizon_le_one) ((carrier L k).stops_after p) hZ
      c (referenceProfile_measurable P Λ u d0) (mul_pos (fraction_pos P) P.lower_pos)
      (referenceProfile_bounds P Λ u d0)] with y hy hrow
  intro A0 ν hA0 hν hjet b hb0 B0 hBDG
  dsimp only
  let cs := assignments (m:=k+1) (List.finRange k)
  let row := heatRow ((carrier L k).observations.observations p) q y
  let mean := fun ω => NativePointAssignmentMoments.actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP θ L k q ω p
  let W := fun choices ω => ∫ x,rangeAssignedWord L c k p q row (mean ω) choices x
    ∂terminalAssignedMeasure L c k p q
  have hm : Measurable mean := by
    exact NativePairWindowLeaf.futureMean_measurable 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S q
      (targets L k p) (unitCenters L k p) (carrier_targets_after L p hages hq) θ
  have hW (choices) (_hc : choices∈cs) : Measurable (W choices) :=
    ActualPointMomentSum.assignment_average_measurable L c k p q row mean hm choices
  have hbound (choices) (hc : choices∈cs) := hy choices
    (ActualPointMomentSum.choices_nodup k choices hc) (ActualPointMomentSum.chosen choices)
    (ActualPointMomentSum.chosen_mem choices) A0 ν hA0 hν
    ((L.test_uniform.smooth _).of_le (by simp))
    (fun j hj z => hjet j (hj.trans (ActualPointMomentSum.root_length_le k choices hc)) z) b hb0 B0 hBDG
  have hsum := FiniteAssignmentMoments.moment_sum μ cs W hW b hb0
    (fun choices hc => (hbound choices hc).1)
    (assignmentConstant (M:=M) Λ κ u₀ v₀ P haP θ L k p q y b B0 A0 ν)
    (fun choices hc => (hbound choices hc).2)
  have he (ω : Ω) : ActualMeanKernel.point L k q
      (NativePointAssignmentMoments.actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP θ L k q ω) p y=
      (1/2:ℝ)^k*(cs.map (fun choices => W choices ω)).sum := by
    rw [ActualMeanKernel.point_of_before L k q _ p y hq]
    exact (hrepresentation q q.2 hq row (mean ω) hrow).2
  have hpow (ω : Ω) : |ActualMeanKernel.point L k q
      (NativePointAssignmentMoments.actualMean 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S P haP θ L k q ω) p y|^(2*b)=
      ((1/2:ℝ)^k)^(2*b)*|(cs.map (fun choices => W choices ω)).sum|^(2*b) := by
    rw [he ω,abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^k),mul_pow]
  constructor
  · exact (hsum.1.const_mul _).congr (ae_of_all _ (fun ω => (hpow ω).symm))
  · simp_rw [hpow]
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hsum.2 (by positivity)).trans_eq (by ring)

end SHE.NativeActualPointMoments
