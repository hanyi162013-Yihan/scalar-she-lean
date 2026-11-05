module

public import SHE.UniformScoreConstants
public import SHE.PhysicalScoreForestAE

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianCoordinates FixedOldScoreSupport OldIntervalCovariance
  MeasurableGaussianScores ScoreProjectionEnergy StoppedGaussianFeatures PhysicalParentGeometry OrderedHeatForests
open scoped BigOperators
local instance uniformPhysicalScoreForest_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def uniformHorizon (n : ℕ) : ℕ→ℝ := fun k=>UniformScoreConstants.horizon (n+k)
def uniformConstant (n : ℕ) : ℕ→ℝ := fun k=>UniformScoreConstants.constant (n+k)

theorem uniformHorizon_pos (n k : ℕ) : 0<uniformHorizon n k := UniformScoreConstants.horizon_pos (n+k)
theorem uniformConstant_pos (n k : ℕ) : 0<uniformConstant n k := UniformScoreConstants.constant_pos (n+k)

/-- Local physical node applicability with fixed dimensional constants,
chosen before all reference profiles and interpolation parameters. -/
theorem uniform_node_score_heat (k : ℕ) :
    let H := uniformHorizon n k
    let C := uniformConstant n k
    ∀ (c : Domain→ℝ),Measurable c → ∀ {ell : ℝ},0<ell →
    (∀ r,ell≤c r ∧ c r≤R.reference r) →
    (∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target) →
    ∀ (p : History P k) (t : ℝ),R.base<t → t<(carrier L k).terminal p →
    (∀ i,((carrier L k).observations.observations p i).target-t≤H) →
    ∀ᵐ x : HeatCircle ∂AddCircle.haarAddCircle,
      scoreVariance (profileCovariances L c k (p,t,x)) (row L k (p,t,x))≤
        (C/(ell*((carrier L k).terminal p-t)))*
          ∑ i : Fin (n+k),‖ProfileVariance.heatPhysical
            (2*(((carrier L k).observations.observations p i).target-t))
            ((carrier L k).observations.observations p i).center x‖ := by
  intro H C
  have hV := UniformScoreConstants.score_heat_kernel (n+k)
  intro c hc ell hell hb hages p t hbase hgap hsmall
  let Z := (carrier L k).observations.observations p
  let σ : Fin (n+k) → ℝ := fun i => (Z i).stop
  let target : Fin (n+k) → ℝ := fun i => (Z i).target
  let center : Fin (n+k) → HeatCircle := fun i => (Z i).center
  have hcb (r : Domain) : ell ≤ c r ∧ c r ≤ R.upper :=
    ⟨(hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have hnode (x : HeatCircle) : (carrier L k).nodeTime (p,t,x)=t :=
    ClippedCovariance.clip_eq ⟨hbase.le,hgap.le⟩
  have hcov : intervalCovariance Z c t ((carrier L k).terminal p)=
      WordRecursion.covariance c Z t ((carrier L k).terminal p) :=
    PhysicalIntervalCovariance.interval_eq_covariance Z c hc
      (fun r => by rw [abs_of_nonneg (hell.le.trans (hcb r).1)]; exact (hcb r).2)
      (RecursiveScoreSupport.carrier_ages L hages k p) ((carrier L k).stops_after p)
      (R.base_nonneg.trans hbase.le) hgap.le
  have hcovx (x : HeatCircle) : profileCovariances L c k (p,t,x)=
      intervalCovariance Z c t ((carrier L k).terminal p) := by
    unfold profileCovariances
    rw [hnode]
    exact hcov.symm
  have hrow (x : HeatCircle) : row L k (p,t,x)=stoppedRow σ target center (t,x) := by
    simp only [row,Interior,hbase,hgap,and_self,ite_true,hnode]
    ext i
    change (ProfileVariance.heatPhysical ((Z i).target-t) (Z i).center x).re =
      if t < (Z i).stop then (ProfileVariance.heatPhysical ((Z i).target-t) (Z i).center x).re else 0
    rw [ite_eq_left (hgap.trans_le ((carrier L k).stops_after p i))]
  have hactive : IntervalHistoryEnergy.active σ ((carrier L k).terminal p)=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact (carrier L k).stops_after p i
  have hh := hV σ target center (RecursiveScoreSupport.carrier_ages L hages k p)
    (R.base_nonneg.trans hbase.le) hgap (fun i => Or.inr ((carrier L k).stops_after p i))
    (fun i _ => hsmall i) c hc hell hcb
  filter_upwards [hh] with x hx
  rw [hcovx,hrow]
  simpa only [hactive,PhysicalScoreChain.intervalCovariance,σ,target,center,Z,C,uniformConstant] using hx


/-- Actual history/spatial Fubini retains the SAME fixed dimensional
constants; changing the profile or its parameter never changes witnesses. -/
theorem uniform_nodeBound_ae (k : ℕ)
    (c : Domain→ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0<ell)
    (hb : ∀ r,ell≤c r ∧ c r≤R.reference r)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ (k+1),
      NodeBound L c ell (uniformHorizon n k) (uniformConstant n k) k p := by
  let H := uniformHorizon n k
  let C := uniformConstant n k
  have hV := uniform_node_score_heat L k
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


/-- Every original ancestor node has the shared dimensional envelope,
under the actual recursive history measure. -/
theorem uniform_allNodeBounds_ae
    (c : Domain→ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0<ell)
    (hb : ∀ r,ell≤c r ∧ c r≤R.reference r)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      AllNodeBounds L c ell (uniformHorizon n) (uniformConstant n) k p := by
  let H := uniformHorizon n
  let C := uniformConstant n
  have hV := fun k=>uniform_nodeBound_ae L k
  induction k with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ k ih =>
    have hprev : ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ (k+1),
        AllNodeBounds L c ell H C k p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := CutoffWordHistories.historyMeasure R μ k)
        (ν := nodeMeasure R)).ae ih
    filter_upwards [hprev,hV k c hc hell hb hages μ] with p hp hcur
    exact ⟨hp,hcur⟩


/-- The literal full physical old-score parent-forest bound with ONE
fixed dimensional horizon/constant family. In particular the witnesses
are uniform before theta, every reference, and every finite word level. -/
theorem uniform_actual_score_forest_ae
    (c : Domain→ℝ) (hc : Measurable c) {ell : ℝ} (hell : 0<ell)
    (hb : ∀ r,ell≤c r ∧ c r≤R.reference r)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ hp : StrictHistory L k p,SmallHistory L (uniformHorizon n) k p →
      scoreProduct L ((carrier L k).observations.observations p) c k p≤
        timeWeight L ell (uniformConstant n) k p*parentDensity 2 (by norm_num) k
          (fun i=>((carrier L k).observations.observations p i).target)
          (carrier_orderedTimes L hages k p hp)
          (fun i=>((carrier L k).observations.observations p i).center) := by
  let H := uniformHorizon n
  let C := uniformConstant n
  have hC := uniformConstant_pos n
  have hV := uniform_allNodeBounds_ae L
  filter_upwards [hV c hc hell hb hages μ k,supported_ae L c hc hell hb hages μ k]
    with p hbound hsup
  intro hp hsmall
  let Z := (carrier L k).observations.observations p
  have hsel : Selection L Z k p (fun i => i) :=
    ⟨fun _ => rfl,fun j hj => False.elim (hj ⟨j,rfl⟩)⟩
  have hh := scoreProduct_heat_bound L c hc hell hb hages H C (fun j => (hC j).le)
    Z (RecursiveScoreSupport.carrier_ages L hages k p) k p (fun i => i)
    (fun _ _ h => h) hsel hp hsmall hbound hsup
  rw [activeHeatProduct_eq_parentDensity L hages Z k p (fun i => i) (fun _ _ h => h) hsel hp] at hh
  exact hh


end SHE.PhysicalScoreChain
