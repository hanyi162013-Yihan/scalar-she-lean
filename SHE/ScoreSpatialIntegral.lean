module

public import SHE.ScoreSpatialStability
public import SHE.ParentHeatFields
public import SHE.PhysicalParentIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry OrderedHeatForests NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def spatialScore (c : StoppedGaussianFeatures.Domain → ℝ) (k : ℕ)
    (p : History P k) (x : Fin k → HeatCircle) : ℝ :=
  scoreProduct L ((carrier L k).observations.observations (replaceSpace k p x)) c k (replaceSpace k p x)

def parentEnvelope
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (x : Fin k → HeatCircle) : ℝ :=
  parentDensity 2 (by norm_num) k
    (fun i => ((carrier L k).observations.observations p i).target)
    (carrier_orderedTimes L hages k p hp)
    (fun i => ((carrier L k).observations.observations (replaceSpace k p x) i).center)

theorem parentEnvelope_continuous
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) :
    Continuous (parentEnvelope L hages k p hp) := by
  have he : parentEnvelope L hages k p hp = fun x =>
      parentDensity 2 (by norm_num) k
        (fun i => ((carrier L k).observations.observations p i).target)
        (carrier_orderedTimes L hages k p hp)
        (values (fun i => (L.observations.observations (rootParameter k p) i).center) k x) := by
    funext x
    exact congrArg (parentDensity 2 (by norm_num) k _ _) (replaceSpace_centers L k p x)
  rw [he]
  exact (parentDensity_continuous _ _ _ _ _).comp (values_continuous _ k)

theorem parentEnvelope_mass
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) :
    (∫ x : Fin k → HeatCircle, parentEnvelope L hages k p hp x
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle))=(Fintype.card (Choices n k) : ℝ) := by
  simp only [parentEnvelope,replaceSpace_centers]
  exact parentDensity_mass _ _ _ _ _ _

/-- The actual score product is integrable in all old locations, with
the exact parent-assignment mass. The AE envelope is retained explicitly
here and discharged by actual history disintegration in the next step. -/
theorem spatialScore_mass (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (W : ℝ)
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k p x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k p x ≤ W*parentEnvelope L hages k p hp x) :
    Integrable (spatialScore L c k p) (Measure.pi (fun _ => AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k → HeatCircle, spatialScore L c k p x
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤ W*(Fintype.card (Choices n k) : ℝ) := by
  have hdom : Integrable (fun x => W*parentEnvelope L hages k p hp x)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
    (continuous_const.mul (parentEnvelope_continuous L hages k p hp)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (spatialScore L c k p) (Measure.pi (fun _ => AddCircle.haarAddCircle)) := by
    apply hdom.mono' (actual_scoreProduct_spatial_measurable L c hc k p).aestronglyMeasurable
    filter_upwards [hn,hb] with x hx hh
    change ‖spatialScore L c k p x‖ ≤ _
    simpa only [Real.norm_of_nonneg hx] using hh
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi hdom hb
  simpa only [integral_const_mul,parentEnvelope_mass] using hh


/-- All old spatial locations retain a terminal heat edge at any actual
observation. Its integrated envelope ends at the original root cylinder. -/
theorem spatialScore_endpoint (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (W : ℝ) (hW : 0 ≤ W)
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k p x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k p x ≤ W*parentEnvelope L hages k p hp x)
    (i : Fin (n+k)) {q : ℝ} (hq : q < (carrier L k).terminal p) (b : HeatCircle) :
    let t := fun j => ((carrier L k).observations.observations p j).target
    let E := fun x : Fin k → HeatCircle =>
      edge (4*(t i-q)) (mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i)))
        (((carrier L k).observations.observations (replaceSpace k p x) i).center) b
    Integrable (fun x => spatialScore L c k p x*E x)
        (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k → HeatCircle, spatialScore L c k p x*E x
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
      W*((Fintype.card (Choices n k) : ℝ)*(Real.sqrt 2)^k*
        ∑ j : Fin n, edge (4*((L.observations.observations (rootParameter k p) j).target-q))
          (mul_pos (by norm_num) (sub_pos.mpr (root_target_after L hages k p hq j)))
          ((L.observations.observations (rootParameter k p) j).center) b) := by
  intro t E
  have hE : Continuous E := by
    have he : E = fun x =>
        edge (4*(t i-q)) (mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i)))
          (values (fun j => (L.observations.observations (rootParameter k p) j).center) k x i) b := by
      funext x
      exact congrArg (fun a => edge _ _ a b) (congrFun (replaceSpace_centers L k p x) i)
    rw [he]
    exact (continuous_edge _).comp
      (((continuous_apply i).comp (values_continuous _ k)).prodMk continuous_const)
  have hEn (x) : 0 ≤ E x := norm_nonneg _
  have hdom : Integrable (fun x => W*parentEnvelope L hages k p hp x*E x)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) :=
    ((continuous_const.mul (parentEnvelope_continuous L hages k p hp)).mul hE).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k p x*E x ≤ W*parentEnvelope L hages k p hp x*E x := by
    filter_upwards [hb] with x hx
    exact mul_le_mul_of_nonneg_right hx (hEn x)
  have hi : Integrable (fun x => spatialScore L c k p x*E x)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
    apply hdom.mono' ((actual_scoreProduct_spatial_measurable L c hc k p).mul hE.measurable).aestronglyMeasurable
    filter_upwards [hn,hmono] with x hx hh
    change ‖spatialScore L c k p x*E x‖ ≤ _
    simpa only [Real.norm_of_nonneg (mul_nonneg hx (hEn x))] using hh
  refine ⟨hi,?_⟩
  have hh := integral_mono_ae hi hdom hmono
  have hparent := parent_spatial_bound L hages k p hp i hq b
  have hmul := mul_le_mul_of_nonneg_left hparent hW
  have he : (∫ x : Fin k → HeatCircle, W*parentEnvelope L hages k p hp x*E x
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      W*(∫ x : Fin k → HeatCircle, parentEnvelope L hages k p hp x*E x
      ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) := by
    simp only [mul_assoc,integral_const_mul]
  exact (hh.trans_eq he).trans hmul

end SHE.PhysicalScoreChain
