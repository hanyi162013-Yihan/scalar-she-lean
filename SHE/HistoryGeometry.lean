module

public import SHE.UniformPhysicalProfileForest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HistoryGeometry
open Set MeasureTheory WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays PhysicalScoreChain PhysicalParentGeometry StoppedGaussianFeatures StoppedFourier
variable {X : Type} [MeasurableSpace X] {R R' : ReferenceData} {n N : ℕ}
variable (L : Level R X n) (L' : Level R' X n)

theorem lower_eq (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (k : ℕ) (h : History X k) : lower L k h=lower L' k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih h.1) i) j
    exact hnode k h

theorem upper_eq (hterminal : ∀ k h,(carrier L k).terminal h=(carrier L' k).terminal h)
    (k : ℕ) (h : History X k) : upper L k h=upper L' k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih h.1) i) j
    exact hterminal k h.1

theorem direction_eq (hinterior : ∀ k h,Interior L k h↔Interior L' k h)
    (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (Q : Fin N→Observation) (k : ℕ) (h : History X k×(ℝ×HeatCircle)) :
    direction L Q k h=direction L' Q k h := by
  classical
  unfold direction
  by_cases hh : Interior L k h
  · simp only [hh,(hinterior k h).mp hh,ite_true]
    rw [hnode k h]
  · simp only [hh,mt (hinterior k h).mpr hh,ite_false]

theorem directions_eq (hinterior : ∀ k h,Interior L k h↔Interior L' k h)
    (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (Q : Fin N→Observation) (k : ℕ) (h : History X k) : directions L Q k h=directions L' Q k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih h.1) i) j
    exact direction_eq L L' hinterior hnode Q k h

theorem covariances_eq (hlo : ∀ k h,lower L k h=lower L' k h)
    (hup : ∀ k h,upper L k h=upper L' k h) (Q : Fin N→Observation) (c : Domain→ℝ)
    (k : ℕ) (h : History X k) : covariances L Q c k h=covariances L' Q c k h := by
  unfold covariances
  rw [hlo k h,hup k h]

theorem scoreProduct_eq (hlo : ∀ k h,lower L k h=lower L' k h)
    (hup : ∀ k h,upper L k h=upper L' k h)
    (Q : Fin N→Observation) (hdir : ∀ k h,directions L Q k h=directions L' Q k h)
    (c : Domain→ℝ) (k : ℕ) (h : History X k) :
    scoreProduct L Q c k h=scoreProduct L' Q c k h := by
  unfold scoreProduct
  rw [covariances_eq L L' hlo hup Q c k h,hdir k h]

theorem strict_iff (hinterior : ∀ k h,Interior L k h↔Interior L' k h)
    (k : ℕ) (h : History X k) : StrictHistory L k h↔StrictHistory L' k h := by
  induction k with
  | zero => rfl
  | succ k ih => exact and_congr (ih h.1) (hinterior k h)

theorem small_iff (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (hobs : ∀ k h,(carrier L k).observations.observations h=(carrier L' k).observations.observations h)
    (H : ℕ→ℝ) (k : ℕ) (h : History X k) : SmallHistory L H k h↔SmallHistory L' H k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (SmallHistory L H k h.1 ∧ _)↔(SmallHistory L' H k h.1 ∧ _)
    rw [ih h.1,hobs k h.1,hnode k h]

theorem timeWeight_eq
    (hterminal : ∀ k h,(carrier L k).terminal h=(carrier L' k).terminal h)
    (hnode : ∀ k h,(carrier L k).nodeTime h=(carrier L' k).nodeTime h)
    (ell : ℝ) (C : ℕ→ℝ) (k : ℕ) (h : History X k) : timeWeight L ell C k h=timeWeight L' ell C k h := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [timeWeight,ih h.1,hterminal k h.1,hnode k h]

theorem historyMeasure_eq (hbase : R.base=R'.base) (horizon : R.horizon=R'.horizon)
    (μ : Measure X) (k : ℕ) : CutoffWordHistories.historyMeasure R μ k=CutoffWordHistories.historyMeasure R' μ k := by
  have hn : nodeMeasure R=nodeMeasure R' := by rw [nodeMeasure,nodeMeasure,hbase,horizon]
  induction k with
  | zero => rfl
  | succ k ih => simp only [CutoffWordHistories.historyMeasure,ih,hn]

end SHE.HistoryGeometry
