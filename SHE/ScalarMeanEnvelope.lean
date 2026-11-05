module

public import SHE.SingleRootSpatialScore
public import SHE.WeightedSpatialMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain OrderedHeatForests NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

def terminalHeat (k : ℕ) (p : History P k) (q : ℝ) (b : HeatCircle)
    (i : Fin (1+k)) (x : Fin k → HeatCircle) : ℝ :=
  ‖ProfileVariance.heatPhysical (4*(((carrier L k).observations.observations p i).target-q))
    (((carrier L k).observations.observations (replaceSpace k p x) i).center) b‖

/-- Positive part is used only off the proved actual score event. Thus
this is an everywhere nonnegative Borel density with the original score
product almost everywhere; no exceptional-set choice is made. -/
def density (c : StoppedGaussianFeatures.Domain → ℝ) (k : ℕ) (p : History P k)
    (q : ℝ) (b : HeatCircle) (x : Fin k → HeatCircle) : ℝ :=
  max (spatialScore L c k p x) 0 * ∑ i : Fin (1+k), Real.sqrt (terminalHeat L k p q b i x)

theorem density_nonneg (c : StoppedGaussianFeatures.Domain → ℝ) (k : ℕ) (p : History P k)
    (q : ℝ) (b : HeatCircle) (x : Fin k → HeatCircle) : 0 ≤ density L c k p q b x :=
  mul_nonneg (le_max_right _ _) (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))

theorem terminalHeat_continuous
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) {q : ℝ} (hq : q < (carrier L k).terminal p)
    (b : HeatCircle) (i : Fin (1+k)) : Continuous (terminalHeat L k p q b i) := by
  have he : terminalHeat L k p q b i = fun x =>
      ‖ProfileVariance.heatPhysical (4*(((carrier L k).observations.observations p i).target-q))
        (values (fun j => (L.observations.observations (rootParameter k p) j).center) k x i) b‖ := by
    funext x
    exact congrArg (fun a => ‖ProfileVariance.heatPhysical _ a b‖)
      (congrFun (replaceSpace_centers L k p x) i)
  rw [he]
  have ht : 0 < 4*(((carrier L k).observations.observations p i).target-q) :=
    mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i))
  exact ((NativeHeatSpan.continuous_heatPhysical_space ht).comp
    (((continuous_apply i).comp (values_continuous _ k)).prodMk continuous_const)).norm

theorem density_measurable (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) {q : ℝ} (hq : q < (carrier L k).terminal p) (b : HeatCircle) :
    Measurable (density L c k p q b) :=
  ((actual_scoreProduct_spatial_measurable L c hc k p).max measurable_const).mul
    (Finset.measurable_sum Finset.univ (fun i _ =>
      Real.continuous_sqrt.measurable.comp (terminalHeat_continuous L hages k p hq b i).measurable))

/-- The full nonnegative scalar first-score spatial density has the
manuscript's actual age-eight kernel mass. All spatial score and range
exceptional sets have already been handled in the actual history. -/
theorem density_mass_bound (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (W : ℝ) (hW : 0 ≤ W)
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k p x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k p x ≤ W*parentEnvelope L hages k p hp x)
    {q : ℝ} (hq : q < (carrier L k).terminal p) (b : HeatCircle) :
    let w := (L.observations.observations (rootParameter k p) 0).target-q
    let a := (L.observations.observations (rootParameter k p) 0).center
    Integrable (density L c k p q b) (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k → HeatCircle,density L c k p q b x
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
      ((1+k:ℕ):ℝ)*(W*(Fintype.card (Choices 1 k) : ℝ)*Real.sqrt ((Real.sqrt 2)^k)*NativeHeatSpan.sqrtKernelConstant)*
        w^(1/4:ℝ)*‖ProfileVariance.heatPhysical (8*w) a b‖ := by
  intro w a
  let f := fun i x => max (spatialScore L c k p x) 0*Real.sqrt (terminalHeat L k p q b i x)
  have hi (i : Fin (1+k)) : Integrable (f i) (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k → HeatCircle,f i x ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
        (W*(Fintype.card (Choices 1 k) : ℝ)*Real.sqrt ((Real.sqrt 2)^k)*NativeHeatSpan.sqrtKernelConstant)*
          w^(1/4:ℝ)*‖ProfileVariance.heatPhysical (8*w) a b‖ := by
    have hh := spatialScore_single_root L c hc hages k p hp W hW hn hb i hq b
    simp only [edge,NativeHeatSpan.kernel_eq_physical] at hh
    have he : (fun x => spatialScore L c k p x*Real.sqrt (terminalHeat L k p q b i x))=ᵐ[
        Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)] f i := by
      filter_upwards [hn] with x hx
      simp only [f,max_eq_left hx]
    exact ⟨hh.1.congr he,(integral_congr_ae he).symm.trans_le hh.2⟩
  have he : density L c k p q b = fun x => ∑ i : Fin (1+k), f i x := by
    funext x
    simp only [density,f,Finset.mul_sum]
  rw [he]
  refine ⟨integrable_finset_sum _ (fun i _ => (hi i).1),?_⟩
  rw [integral_finsetSum _ (fun i _ => (hi i).1)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (1+k)))) => (hi i).2)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hh

end SHE.ScalarMeanEnvelope
