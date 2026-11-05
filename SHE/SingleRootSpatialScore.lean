module

public import SHE.ScoreSpatialCauchy
public import SHE.NativeHeatRoot

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry OrderedHeatForests NativeHeatAction
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

/-- The scalar original root gives precisely the positive age-eight heat
shape needed to normalize the actual mean kernel. No square is applied to
an old score energy, so every old time-gap power remains unchanged. -/
theorem spatialScore_single_root (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) (W : ℝ) (hW : 0 ≤ W)
    (hn : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      0 ≤ spatialScore L c k p x)
    (hb : ∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
      spatialScore L c k p x ≤ W*parentEnvelope L hages k p hp x)
    (i : Fin (1+k)) {q : ℝ} (hq : q < (carrier L k).terminal p) (b : HeatCircle) :
    let t := fun j => ((carrier L k).observations.observations p j).target
    let E := fun x : Fin k → HeatCircle =>
      edge (4*(t i-q)) (mul_pos (by norm_num) (sub_pos.mpr (carrier_targets_after L p hages hq i)))
        (((carrier L k).observations.observations (replaceSpace k p x) i).center) b
    let w := (L.observations.observations (rootParameter k p) 0).target-q
    let a := (L.observations.observations (rootParameter k p) 0).center
    Integrable (fun x => spatialScore L c k p x*Real.sqrt (E x))
        (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ∧
      (∫ x : Fin k → HeatCircle, spatialScore L c k p x*Real.sqrt (E x)
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
      (W*(Fintype.card (Choices 1 k) : ℝ)*Real.sqrt ((Real.sqrt 2)^k)*NativeHeatSpan.sqrtKernelConstant)*
        w^(1/4:ℝ)*‖ProfileVariance.heatPhysical (8*w) a b‖ := by
  intro t E w a
  have hh := spatialScore_sqrt_endpoint L c hc hages k p hp W hW hn hb i hq b
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hw : 0 < w := sub_pos.mpr (root_target_after L hages k p hq 0)
  have hsum : (∑ j : Fin 1,
      edge (4*((L.observations.observations (rootParameter k p) j).target-q))
        (mul_pos (by norm_num) (sub_pos.mpr (root_target_after L hages k p hq j)))
        ((L.observations.observations (rootParameter k p) j).center) b) =
      ‖ProfileVariance.heatPhysical (4*w) a b‖ := by
    simp only [Fin.sum_univ_one,edge,NativeHeatSpan.kernel_eq_physical,w,a]
  rw [hsum,Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) k)]
  have hnonneg : 0 ≤ W*(Fintype.card (Choices 1 k) : ℝ)*Real.sqrt ((Real.sqrt 2)^k) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (NativeHeatSpan.sqrt_kernel_four_eight hw a b) hnonneg
  convert! hb' using 1 <;> ring

end SHE.PhysicalScoreChain
