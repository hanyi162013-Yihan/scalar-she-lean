module

public import SHE.JointUncutLocalRemainder
public import SHE.JointRecursiveCutoffCorrection
public import SHE.JointHeatLeafLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.JointUncutSuccessor
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open JointUncutEvaluationLimit JointUncutWordEvaluation JointUncutLocalRemainder Topology
open CutoffCarriers CutoffUncutComparison UncutWordEvaluation Classical
local instance : MeasurableSpace CircleL2:=borel _
local instance : BorelSpace CircleL2:=⟨rfl⟩
variable {P Ω:Type} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R:ReferenceData} {n:ℕ} (L:Level R P n) (Λ:ℝ)
variable (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)
variable (hU:Measurable U) (hV:Measurable V) (hXU:Measurable XU) (hXV:Measurable XV)
variable (ν:Measure P) [IsFiniteMeasure ν]

include hU hV hXU hXV in
/-- After the time cutoff is removed, the actual local insertion is
exactly the next physical leaf, before any sample expectation. -/
theorem averaged_eq (k:ℕ) (ω:Ω):
    (∫p,JointUncutLocalRemainder.value L Λ U V XU XV k p ω ∂historyMeasure R ν k)=
      ∫p,JointUncutWordEvaluation.leaf L Λ U V XU XV (k+1) p ω ∂historyMeasure R ν (k+1):=by
  let σ:=historyMeasure R ν k
  let σs:=historyMeasure R ν (k+1)
  let A:=fun δ:ℝ=>∫p,JointUncutLocalRemainder.cutoff L Λ U V XU XV δ k p ω ∂σ
  let B:=fun δ:ℝ=>∫p,cutoffLeaf L Λ U V XU XV δ (k+1) p ω ∂σs
  let C:=fun δ:ℝ=>if hδ:0<δ then
    ∫p,JointCutoffStep.correction (RecursiveHeatBounds.level L δ hδ 0 k) Λ δ U V XU XV p ω ∂σ else 0
  obtain ⟨Ca,hCa,hCab⟩:=JointUncutLocalRemainder.bound L Λ U V XU XV k
  have hl:Tendsto A (𝓝[>] (0:ℝ))
      (𝓝 (∫p,JointUncutLocalRemainder.value L Λ U V XU XV k p ω ∂σ)):=by
    apply DominatedCutoffLimit.integral_tendsto σ
      (W:=UncutSmoothWords.weight L k) (M:=Ca) (UncutHistoryMass.weight_integrable L ν k)
    · intro δ hδ
      have hm:=JointWordAnalytic.remainder_measurable (RecursiveHeatBounds.level L δ hδ 0 k) Λ hU hV hXU hXV
      simp only [JointUncutLocalRemainder.cutoff,dite_eq_left hδ]
      convert! hm.comp (measurable_id.prodMk measurable_const) using 1
    · intro δ hδ p
      rw [JointUncutLocalRemainder.cutoff_eq L Λ U V XU XV hδ]
      split_ifs
      · exact hCab p ω
      · exact (norm_zero).le.trans (mul_nonneg hCa (UncutSmoothWords.weight_nonneg L k p))
    · intro p
      obtain ⟨η,hη,hEq⟩:=eventually_test_eq L k p
      refine ⟨η,hη,fun δ hδ hd=>?_⟩
      rw [JointUncutLocalRemainder.cutoff,dite_eq_left hδ]
      apply JointLocalTestScaling.remainder_smul (RecursiveHeatBounds.level L δ hδ 0 k)
        (normalizedLevel L k) Λ U V XU XV (UncutSmoothWords.weight L k p) p ω
        (observations_eq L hδ zero_lt_one k p) (CutoffCarriers.terminal_eq L hδ zero_lt_one k p)
      rw [hEq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized]
      rfl
  obtain ⟨Cb,hCb,hCbb,_⟩:=evaluation_norm_bounds L Λ U V XU XV (k+1)
  have hb:Tendsto B (𝓝[>] (0:ℝ))
      (𝓝 (∫p,leaf L Λ U V XU XV (k+1) p ω ∂σs)):=by
    apply DominatedCutoffLimit.integral_tendsto σs
      (W:=UncutSmoothWords.weight L (k+1)) (M:=Cb) (UncutHistoryMass.weight_integrable L ν (k+1))
    · intro δ hδ
      have hm:=JointWordAnalytic.leaf_measurable (RecursiveHeatBounds.level L δ hδ 0 (k+1)) Λ hU hV hXU hXV
      simp only [cutoffLeaf,dite_eq_left hδ]
      convert! hm.comp (measurable_id.prodMk measurable_const) using 1
    · intro δ hδ p
      rw [cutoffLeaf,dite_eq_left hδ,cutoff_leaf_eq L Λ U V XU XV hδ]
      split_ifs
      · exact hCbb p ω
      · exact (norm_zero).le.trans (mul_nonneg hCb (UncutSmoothWords.weight_nonneg L (k+1) p))
    · exact fun p=>leaf_eventually_eq L Λ U V XU XV (k+1) p ω
  obtain ⟨K,hK,hKb⟩:=JointRecursiveCutoffCorrection.weighted_correction_bound L Λ hU hV hXU hXV k
  have hc:Tendsto C (𝓝[>] (0:ℝ)) (𝓝 0):=by
    have ht:Tendsto (fun δ:ℝ=>K*(∫p,UncutSmoothWords.weight L k p ∂σ)*PhysicalRemainderMass.heatMass δ)
        (𝓝[>] (0:ℝ)) (𝓝 0):=by
      have hh:=((continuous_const (y:=K*(∫p,UncutSmoothWords.weight L k p ∂σ))).mul
        PhysicalBoundaryStrip.continuous_heatMass).tendsto (0:ℝ)
      have hr:=hh.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
      change Tendsto (fun δ:ℝ=>K*(∫p,UncutSmoothWords.weight L k p ∂σ)*PhysicalRemainderMass.heatMass δ)
        (𝓝[>] (0:ℝ)) (𝓝 (K*(∫p,UncutSmoothWords.weight L k p ∂σ)*PhysicalRemainderMass.heatMass 0)) at hr
      simpa only [PhysicalRemainderMass.heatMass,Real.zero_rpow (by norm_num : (1/2:ℝ)≠0),mul_zero,add_zero] using hr
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ht
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0<δ at hδ
    dsimp only [C]
    rw [dite_eq_left hδ]
    have hd:Integrable (fun p=>K*PhysicalRemainderMass.heatMass δ*UncutSmoothWords.weight L k p) σ:=
      (UncutHistoryMass.weight_integrable L ν k).const_mul _
    have he:=norm_integral_le_of_norm_le hd (Eventually.of_forall (fun p=>by
      convert hKb δ hδ p ω using 1 <;> ring))
    exact he.trans_eq (by rw [integral_const_mul];ring)
  have he:∀ᶠδ in 𝓝[>] (0:ℝ),A δ=B δ+C δ:=by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0<δ at hδ
    let Q:=RecursiveHeatBounds.level L δ hδ 0 k
    have hm:=JointCutoffStep.childLeaf_measurable Q Λ δ hU hV hXU hXV hδ
    obtain ⟨D,hD,hDb⟩:=JointCutoffStep.childLeaf_uniform_bound Q Λ δ (U:=U) (V:=V) (XU:=XU) (XV:=XV) hδ
    have hi:Integrable (fun z:History P k×(ℝ×HeatCircle)=>JointCutoffStep.childLeaf Q Λ δ U V XU XV z ω)
        (σ.prod (nodeMeasure R)):=
      (integrable_const D).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall (fun z=>hDb z ω))
    have hmi:=JointWordAnalytic.remainder_measurable Q Λ hU hV hXU hXV
    obtain ⟨D',hD',hD'b⟩:=JointInsertionBounds.uniform_level_bound Q Λ U V XU XV
    have hri:Integrable (fun p=>JointWordAnalytic.remainder Q Λ U V XU XV p ω) σ:=
      (integrable_const D').mono' (hmi.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall (fun p=>(hD'b p ω).2.2))
    have hbe:B δ=∫z:History P k×(ℝ×HeatCircle),JointCutoffStep.childLeaf Q Λ δ U V XU XV z ω
        ∂σ.prod (nodeMeasure R):=by
      apply integral_congr_ae
      filter_upwards with z
      rw [cutoffLeaf,dite_eq_left hδ]
      change JointCutoffStep.heatChildLeaf Q Λ δ U V XU XV 0 z ω=_
      exact JointHeatLeafLimit.heatChild_zero_eq_literal δ Λ Q U V XU XV z ω
    rw [hbe]
    dsimp only [C]
    rw [dite_eq_left hδ]
    dsimp only [A,JointUncutLocalRemainder.cutoff]
    simp only [dite_eq_left hδ]
    change (∫p,JointWordAnalytic.remainder Q Λ U V XU XV p ω ∂σ)=_
    have hs:=integral_sub hri hi.integral_prod_left
    rw [integral_prod _ hi]
    dsimp only [JointCutoffStep.correction]
    linarith only [hs]
  have ht:= (hb.add hc).congr' (he.mono (fun δ h=>h.symm))
  have hh:=tendsto_nhds_unique hl ht
  simpa only [add_zero] using hh

end SHE.JointUncutSuccessor
