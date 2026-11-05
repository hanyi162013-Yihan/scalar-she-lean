module

public import SHE.PhysicalNodeScoreFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers FixedOldScoreSupport MeasurableGaussianScores StoppedGaussianFeatures
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def NodeBound (c : Domain → ℝ) (ell H C : ℝ) (k : ℕ) (p : History P (k+1)) : Prop :=
  Interior L k p →
    (∀ i, ((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p ≤ H) →
    nodeEnergy L c k p ≤ (C/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p)))*nodeHeat L k p

set_option backward.isDefEq.respectTransparency false in
theorem nodeBound_measurableSet (c : Domain → ℝ) (hc : Measurable c) (ell H C : ℝ) (k : ℕ) :
    MeasurableSet {p | NodeBound L c ell H C k p} := by
  have hs : MeasurableSet {p : History P (k+1) | ∀ i,
      ((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p ≤ H} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le
      ((((carrier L k).observations.target_measurable i).comp measurable_fst).sub
        (carrier L k).nodeTime_measurable) measurable_const
  have hp : Measurable (fun p : History P (k+1) =>
      C/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p))) :=
    measurable_const.div (measurable_const.mul
      (((carrier L k).terminal_measurable.comp measurable_fst).sub (carrier L k).nodeTime_measurable))
  have hb := measurableSet_le (nodeEnergy_measurable L c hc k) (hp.mul (nodeHeat_measurable L k))
  have hi : MeasurableSet {p : History P (k+1) | Interior L k p} := interior_measurableSet L k
  have hm := (hi.inter hs).compl.union hb
  have he : {p : History P (k+1) | NodeBound L c ell H C k p} =
      (({p : History P (k+1) | Interior L k p} ∩
        {p : History P (k+1) | ∀ i,
          ((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p ≤ H})ᶜ ∪
        {p : History P (k+1) | nodeEnergy L c k p ≤
          (C/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p)))*nodeHeat L k p}) := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_inter_iff,NodeBound]
    tauto
  rw [he]
  simpa only [Pi.mul_apply] using hm

/-- Genuine history/spatial Fubini for the local-frame score envelope.
The later random observation centers are never substituted into a fixed
frame's exceptional set. All events used for Fubini are proved Borel. -/
theorem nodeBound_ae (k : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
    ∀ (c : Domain → ℝ), Measurable c → ∀ {ell : ℝ}, 0 < ell →
    (∀ r, ell ≤ c r ∧ c r ≤ R.reference r) →
    (∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ],
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ (k+1), NodeBound L c ell H C k p := by
  obtain ⟨H,C,hH,hC,hV⟩ := node_score_heat L k
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell hell hb hages μ _
  apply (Measure.ae_prod_iff_ae_ae (nodeBound_measurableSet L c hc ell H C k)).mpr
  apply ae_of_all
  intro p
  apply (Measure.ae_prod_iff_ae_ae
    ((nodeBound_measurableSet L c hc ell H C k).preimage
      (measurable_const.prodMk measurable_id))).mpr
  apply ae_of_all
  intro t
  have hnode (h : R.base < t ∧ t < (carrier L k).terminal p) (x : HeatCircle) :
      (carrier L k).nodeTime (p,t,x)=t := ClippedCovariance.clip_eq ⟨h.1.le,h.2.le⟩
  by_cases ht : R.base < t ∧ t < (carrier L k).terminal p
  · by_cases hs : ∀ i, ((carrier L k).observations.observations p i).target-t ≤ H
    · filter_upwards [hV c hc hell hb hages p t ht.1 ht.2 hs] with x hx
      intro _ _
      simpa only [id_eq,nodeEnergy,nodeHeat,hnode ht] using hx
    · exact ae_of_all _ (fun x _ hsmall => False.elim
        (hs (by simpa only [id_eq,hnode ht] using hsmall)))
  · exact ae_of_all _ (fun _ hi _ => False.elim (ht hi))

end SHE.PhysicalScoreChain
