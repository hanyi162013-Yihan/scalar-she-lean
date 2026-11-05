module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.ControlledReferenceRecursiveAverages
public import SHE.ControlledReferenceRecursiveWeights
public import SHE.HeatFieldMovingWeight
public import SHE.HeatMassCongruence
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointStateSpatialLimit
public import SHE.PastParameterDiagonal
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRandomSpatialLimit
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open Filter Topology
open scoped NNReal
local instance controlledReferenceRandomSpatialLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRandomSpatialLimit_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRandomSpatialLimit_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local instance controlledReferenceRandomSpatialLimit_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ] {H : ℝ≥0}
variable (dU dV : PredictableWordState.Data 𝓕 τ H)

theorem nodeState_all_eq (p p' : Inputs) (ε η : ℝ≥0) (k : ℕ) :
    JointStateSpatialLimit.nodeState (L p ε k) dV=JointStateSpatialLimit.nodeState (L p' η k) dV := by
  funext q
  change dV.state ((ClippedCovariance.clip (v:ℝ) ((L p ε k).terminal q.1.1) q.2).toNNReal,q.1.2)=
    dV.state ((ClippedCovariance.clip (v:ℝ) ((L p' η k).terminal q.1.1) q.2).toNNReal,q.1.2)
  rw [ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε η k q.1.1]

/-- Pointwise physical identification for a genuinely random reference
weight. This is separated from the subsequent product-measure limit so
its dependent profile/state conversions are checked once. -/
theorem child_difference_mass (u : Ω→Inputs) (ε : ℝ) (hε : 0<ε) (k : ℕ) (q : (History Unit k×Ω)×ℝ) :
    (∫ x : HeatCircle,
      |JointCutoffStep.heatChildLeaf (L (u q.1.2) ε.toNNReal k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField ε (q.1.1,(q.2,x)) q.1.2-
        JointCutoffStep.childLeaf (L (u q.1.2) ε.toNNReal k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (q.1.1,(q.2,x)) q.1.2|
      ∂AddCircle.haarAddCircle)=
      HeatFieldWeightedLimit.mass (JointStateSpatialLimit.nodeState (L (0,0) 0 k) dV) A
        (fun z : ((History Unit k×Ω)×ℝ)×HeatCircle =>
          JointStateSpatialLimit.weight (L (u z.1.1.2) ε.toNNReal k) dU dV Λ δ z) ε q := by
  let Uε := JointStateSpatialLimit.nodeState (L (u q.1.2) ε.toNNReal k) dV
  let U₀ := JointStateSpatialLimit.nodeState (L (0,0) 0 k) dV
  let Dε := JointStateSpatialLimit.weight (L (u q.1.2) ε.toNNReal k) dU dV Λ δ
  let D := fun z : ((History Unit k×Ω)×ℝ)×HeatCircle =>
    JointStateSpatialLimit.weight (L (u z.1.1.2) ε.toNNReal k) dU dV Λ δ z
  have hh := JointStateSpatialLimit.child_difference_mass (L (u q.1.2) ε.toNNReal k) dU dV Λ δ ε hε q
  have hs : Uε q=U₀ q := congrFun
    (nodeState_all_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dV (u q.1.2) (0,0) ε.toNNReal 0 k) q
  have h₁ := HeatMassCongruence.state Uε U₀ A Dε ε q hs
  have h₂ := HeatMassCongruence.weight U₀ A Dε D ε q (fun _ => rfl)
  exact hh.trans (h₁.trans h₂)

include hsmall in
/-- The actual heat-versus-literal newest-leaf error vanishes in full
history/sample/time/space L¹ even when the ENTIRE reference and every
recursive Hessian weight depend on the original random past states.
This uses actual spatial heat approximation, not pointwise convergence
of zero-age L² representatives. -/
theorem integrated_child_difference_tendsto_zero (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u)
    (ν : Measure (History Unit 0)) [IsFiniteMeasure ν] (k : ℕ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Tendsto (fun ε : ℝ => ∫ q : (History Unit k×Ω)×ℝ,
      ∫ x : HeatCircle,
        |JointCutoffStep.heatChildLeaf (L (u q.1.2) ε.toNNReal k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField ε (q.1.1,(q.2,x)) q.1.2-
          JointCutoffStep.childLeaf (L (u q.1.2) ε.toNNReal k) Λ δ dU.physicalState dV.physicalState dU.physicalField dV.physicalField (q.1.1,(q.2,x)) q.1.2|
        ∂AddCircle.haarAddCircle
      ∂((CutoffWordHistories.historyMeasure (R (0,0)) ν k).prod μ).prod (volume.restrict (Ioc (v:ℝ) (b:ℝ))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRecursiveWeights.weight_bounded P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV k
  obtain ⟨M,hM⟩ := hA.norm_bound
  obtain ⟨B,hB⟩ := hA.fderiv.norm_bound
  have hBn : 0≤B := (norm_nonneg _).trans (hB 0)
  have hLip (z w : ℝ) : |A z-A w|≤B*|z-w| := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hA.smooth.differentiable (by simp) y) (fun y _ => hB y) convex_univ (mem_univ w) (mem_univ z)
  let state := JointStateSpatialLimit.nodeState (L (0,0) 0 k) dV
  let weight := fun (ε : ℝ) (q : ((History Unit k×Ω)×ℝ)×HeatCircle) =>
    JointStateSpatialLimit.weight (L (u q.1.1.2) ε.toNNReal k) dU dV Λ δ q
  have hwm (ε : ℝ) : Measurable (weight ε) :=
    ControlledReferenceRecursiveWeights.weight_diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall dU dV hΛ u hu ε.toNNReal k
  have ht := HeatFieldMovingWeight.integrated_mass_tendsto_zero state
    (JointStateSpatialLimit.nodeState_measurable (L (0,0) 0 k) dV) A hA.smooth.continuous.measurable weight hwm
    (((CutoffWordHistories.historyMeasure (R (0,0)) ν k).prod μ).prod (volume.restrict (Ioc (v:ℝ) (b:ℝ))))
    (fun z => by simpa only [Real.norm_eq_abs] using hM z) hCn
    (fun ε q => hC (u q.1.1.2) ε.toNNReal q) hBn hLip
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  filter_upwards with q
  exact (child_difference_mass P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV u ε hε k q).symm

end SHE.ControlledReferenceRandomSpatialLimit
