module

public import SHE.TerminalSuccessorGeometry
public import SHE.RelativeHistoryGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.TerminalConditionalGeometry
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain CoveredControlledLaw CoveredHistoryGeometry
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n k r m:ℕ}

/-- The geometric inputs to the already proved conditional endpoint
Gaussian estimates. All data remain original stopped observations. -/
structure Packet (q ageBound:ℝ) (σ target:Fin n→ℝ) (lo hi:Fin r→ℝ)
    (leaf:Fin m→Fin (n+1)) : Prop where
  stop_pos:∀i,0<σ i
  stop_le_one:∀i,σ i≤1
  ages:∀i,σ i≤target i
  target_after:∀i,q<target i
  lower:∀j,q≤lo j
  intervals:∀j,lo j<hi j
  stops:∀j i,σ i≤lo j ∨ hi j≤σ i
  disjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j
  native:∀j,(Fin.cons q σ:Fin (n+1)→ℝ) (leaf j)=
    (Fin.cons q target:Fin (n+1)→ℝ) (leaf j)
  leaf_age:∀j,(Fin.cons q target:Fin (n+1)→ℝ) (leaf j)∈Ioc 0 ageBound

/-- Strict ORIGINAL histories discharge every endpoint packet
hypothesis, including the newest zero-future-age rough leaf. -/
theorem packet (L:Level R X n)
    (hages:∀x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target)
    (T ageBound:ℝ) (hterm:∀x,L.terminal x≤T)
    (hspan1:T-R.base≤1) (hspan:T-R.base≤ageBound)
    (k:ℕ) (h:History X (k+1)) (hp:StrictHistory L (k+1) h):
    Packet ((carrier L k).nodeTime h-R.base) ageBound
      (fun i=>stops L k h.1 i-R.base) (fun i=>targets L k h.1 i-R.base)
      (fun j=>lower L (k+1) h j-R.base) (fun j=>upper L (k+1) h j-R.base)
      (leafIndex (k+1) (fun i=>i)):=by
  have he:(carrier L k).nodeTime h=h.2.1:=ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
  have hqbase:R.base<(carrier L k).nodeTime h:=by rw [he];exact hp.2.1
  have hqt:(carrier L k).nodeTime h<(carrier L k).terminal h.1:=by rw [he];exact hp.2.2
  have hs:=(TerminalSuccessorGeometry.stops_succ L k h)
  have ht:=(TerminalSuccessorGeometry.targets_succ L k h)
  have hsrel:(fun i=>stops L (k+1) h i-R.base)=
      Fin.cons ((carrier L k).nodeTime h-R.base) (fun i=>stops L k h.1 i-R.base):=by
    rw [hs]
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  have htrel:(fun i=>targets L (k+1) h i-R.base)=
      Fin.cons ((carrier L k).nodeTime h-R.base) (fun i=>targets L k h.1 i-R.base):=by
    rw [ht]
    funext i
    exact Fin.cases rfl (fun _=>rfl) i
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RelativeHistoryGeometry.relative_stop_pos L k h.1 hqbase.le hqt
  · intro i
    exact (RelativeHistoryGeometry.relative_stop_le_span L T hterm k h.1 i).trans hspan1
  · intro i
    exact sub_le_sub_right ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages L hages k h.1 i)) _
  · intro i
    exact sub_lt_sub_right (carrier_targets_after L h.1 hages hqt i) _
  · intro j
    exact sub_le_sub_right (terminal_le_lower L (k+1) h j) _
  · intro j
    exact sub_lt_sub_right (lower_lt_upper L (k+1) h hp j) _
  · intro j i
    exact RelativeHistoryGeometry.relative_stop_dichotomy L (k+1) h j i.succ
  · exact RelativeHistoryGeometry.relative_disjoint L (k+1) h
  · intro j
    have hj:=congrArg (fun z:ℝ=>z-R.base) (RelativeHistoryGeometry.native_leaf L (k+1) h hp j)
    rw [←hsrel,←htrel]
    exact hj
  · intro j
    have hm:R.base≤(R.base+(carrier L k).nodeTime h)/2:=by linarith
    have hmq:(R.base+(carrier L k).nodeTime h)/2<(carrier L (k+1)).terminal h:=by
      change (R.base+(carrier L k).nodeTime h)/2<(carrier L k).nodeTime h
      linarith
    have hj:=RelativeHistoryGeometry.native_leaf_relative_age L T ageBound hterm hspan
      (k+1) h hp hm hmq j
    rw [←htrel]
    exact hj

end SHE.TerminalConditionalGeometry
