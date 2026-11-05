module

public import SHE.HistoryProductMeasure
public import SHE.CoveredHistoryGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SHE.HistoryHorizonIntegration
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry CoveredHistoryGeometry PhysicalChainArrays PhysicalScoreChain
open Classical
variable {X:Type} [MeasurableSpace X]

def box (T:ℝ):(k:ℕ)→Set (History X k)
  | 0=>univ
  | k+1=>box T k ×ˢ (Iic T ×ˢ univ)

theorem box_measurable (T:ℝ) (k:ℕ):MeasurableSet (box (X:=X) T k):=by
  induction k with
  | zero=>exact MeasurableSet.univ
  | succ k ih=>exact ih.prod (measurableSet_Iic.prod MeasurableSet.univ)

variable (R Q:ReferenceData) (hb:R.base=Q.base) (hH:R.horizon≤Q.horizon)
include hb hH

theorem node_measure:
    nodeMeasure R=(nodeMeasure Q).restrict (Iic R.horizon ×ˢ univ):=by
  unfold nodeMeasure
  rw [←Measure.prod_restrict,Measure.restrict_univ,Measure.restrict_restrict measurableSet_Iic]
  rw [hb]
  congr 2
  ext t
  simp only [mem_inter_iff,mem_Iic,mem_Ioc]
  constructor
  · rintro ⟨ha,ht⟩
    exact ⟨ht,ha,ht.trans hH⟩
  · rintro ⟨ht,ha,hQ⟩
    exact ⟨ha,ht⟩

theorem history_measure (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    historyMeasure R ρ k=(historyMeasure Q ρ k).restrict (box R.horizon k):=by
  induction k with
  | zero=>exact Measure.restrict_univ.symm
  | succ k ih=>
    change (historyMeasure R ρ k).prod (nodeMeasure R)=_
    rw [ih,node_measure R Q hb hH,Measure.prod_restrict]
    rfl

/-- Changing only the ambient history horizon introduces NO initial
strip: a field supported by the literal ordered history is identical
under both original history measures. -/
theorem integral_eq (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ) (f:History X k→ℝ)
    (hf:∀p,p∉box R.horizon k→f p=0):
    (∫p,f p ∂historyMeasure R ρ k)=∫p,f p ∂historyMeasure Q ρ k:=by
  rw [history_measure R Q hb hH ρ k,←integral_indicator (box_measurable R.horizon k)]
  congr 1
  apply indicator_eq_self.2
  intro p hp
  by_contra hn
  exact hp (hf p hn)

variable {R Q}

omit hb hH in
theorem strict_mem {n:ℕ} (L:Level R X n) (T:ℝ) (hT:∀x,L.terminal x≤T)
    (k:ℕ) (p:History X k) (hp:StrictHistory L k p):p∈box T k:=by
  induction k with
  | zero=>exact mem_univ p
  | succ k ih=>
    refine ⟨ih p.1 hp.1,?_,mem_univ _⟩
    have ht:initialTerminal L k p.1≤T:=hT (rootParameter k p.1)
    exact hp.2.2.le.trans ((terminal_le_initial L k p.1).trans ht)

end SHE.HistoryHorizonIntegration
