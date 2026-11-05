module

public import SHE.VariableFiniteMarkFields
public import SHE.PhysicalFullResidualScore
public import SHE.PredictablePhysicalFields
public import SHE.ActualMeanKernel
public import SHE.CoveredControlledLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.ActualCovarianceMarkFields
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement GaussianConvolution
  StoppedFourier StoppedGaussianFeatures WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalChainArrays CoveredControlledLaw HistoryProductMeasure PhysicalParentGeometry
open scoped BigOperators NNReal
local instance actualCovarianceMarkFields_periodPos : Fact (0<2*π) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {Ω X W : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R X n)

/-- Borel extension outside the actual q<terminal domain. It agrees with
fullResidualCovariance on every active physical history. -/
def cappedResidual (c : Domain→ℝ) (k : ℕ) (p : History X k) (q : ℝ) :=
  fullResidualCovariance L c k p (min q ((carrier L k).terminal p))

theorem cappedResidual_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ) :
    Measurable (fun z : History X k×ℝ=>cappedResidual L c k z.1 z.2) := by
  let Z : VariableObservations.Family (History X k×ℝ) (n+k) :=
    { observations := fun z=>(carrier L k).observations.observations z.1
      stop_measurable := fun i=>((carrier L k).observations.stop_measurable i).comp measurable_fst
      target_measurable := fun i=>((carrier L k).observations.target_measurable i).comp measurable_fst
      center_measurable := fun i=>((carrier L k).observations.center_measurable i).comp measurable_fst }
  have ht := (carrier L k).terminal_measurable.comp (measurable_fst : Measurable (Prod.fst : History X k×ℝ→History X k))
  have hA := Z.covariance_measurable (R.reference_measurable.comp measurable_snd)
    (measurable_snd.min ht) ht (fun _=>min_le_right _ _)
  apply Measurable.of_eval_matrix
  intro i j
  have hres : Measurable (fun z : History X k×ℝ=>∑ l,covariances L
      ((carrier L k).observations.observations z.1) (fun r=>R.reference r-c r) k z.1 l i j) :=
    Finset.measurable_sum Finset.univ (fun l _=>
      ((old_covariances_measurable L _ (R.reference_measurable.sub hc) k l).eval_matrix).comp measurable_fst)
  have hAe : Measurable (fun z : History X k×ℝ=>WordRecursion.covariance R.reference
      ((carrier L k).observations.observations z.1) (min z.2 ((carrier L k).terminal z.1))
      ((carrier L k).terminal z.1) i j) := hA.eval_matrix
  convert! hAe.add hres using 1
  simp only [cappedResidual,fullResidualCovariance,Matrix.add_apply,Matrix.sum_apply]
  rfl

/-- Literal full covariance mark of the actual old average, with each
original stopped row retained and the active q-window stated explicitly. -/
def point (c e : Domain→ℝ) (k : ℕ) (q : ℝ) (m : WordRecursion.State (n+k)) (p : History X k) : ℝ :=
  if q<(carrier L k).terminal p then
    FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
      (fullResidualCovariance L c k p q) e
      (stoppedRow (stops L k p) (targets L k p) (centers L k p)) (oldAverage L c k p) m
  else 0

def coveredFamily (k : ℕ) : VariableObservations.Family (History X k) (n+k) :=
  { observations := fun p i=>⟨stops L k p i,targets L k p i,centers L k p i⟩
    stop_measurable := fun i=>((carrier L k).observations.stop_measurable i).min
      (L.terminal_measurable.comp (rootParameter_measurable k))
    target_measurable := (carrier L k).observations.target_measurable
    center_measurable := (carrier L k).observations.center_measurable }

/-- All root, old history, current mean, lower cutoff and signed profile
input parameters may be dependent. The point mark is a genuine Borel field. -/
theorem point_variable_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ)
    (p : W→History X k) (hp : Measurable p) (q : W→ℝ) (hq : Measurable q)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m)
    (e : W×Domain→ℝ) (he : Measurable e) :
    Measurable (fun w=>point L c (fun r=>e (w,r)) k (q w) (m w) (p w)) := by
  classical
  have hA := (cappedResidual_measurable L c hc k).comp (hp.prodMk hq)
  have hF : Measurable (fun z : W×WordRecursion.State (n+k)=>oldAverage L c k (p z.1) z.2) := by
    convert! (oldAverage_measurable L c hc k).comp
      ((hp.comp measurable_fst).prodMk measurable_snd) using 1
  have hrow : Measurable (fun z : W×Domain=>stoppedRow
      (stops L k (p z.1)) (targets L k (p z.1)) (centers L k (p z.1)) z.2) := by
    convert! (StoppedGaussianFields.row_measurable (coveredFamily L k)).comp
      ((hp.comp measurable_fst).prodMk measurable_snd) using 1
  have hG := VariableFiniteMarkFields.history_covariance_mark_measurable
    (fun w=>cappedResidual L c k (p w) (q w)) hA
    (fun z=>oldAverage L c k (p z.1) z.2) hF m hm
    (fun z=>stoppedRow (stops L k (p z.1)) (targets L k (p z.1)) (centers L k (p z.1)) z.2)
    hrow e he q hq
  have hset : MeasurableSet {w : W | q w<(carrier L k).terminal (p w)} :=
    measurableSet_lt hq ((carrier L k).terminal_measurable.comp hp)
  convert! hG.ite hset (measurable_const (a:=(0:ℝ))) using 1
  funext w
  simp only [point]
  split_ifs with h
  · simp only [cappedResidual,min_eq_left h.le]
  · rfl
  all_goals infer_instance

/-- Direct joint-time specialization, suitable for genuine history/space
and noise Fubini. -/
theorem point_time_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ)
    (m : Ω→History X k→ℝ→WordRecursion.State (n+k))
    (hm : Measurable (fun z : (Ω×History X k)×ℝ=>m z.1.1 z.1.2 z.2))
    (e : ((Ω×History X k)×ℝ)×Domain→ℝ) (he : Measurable e) :
    Measurable (fun z : (Ω×History X k)×ℝ=>point L c (fun r=>e (z,r)) k z.2
      (m z.1.1 z.1.2 z.2) z.1.2) :=
  point_variable_measurable L c hc k (fun z=>(z.1).2) measurable_fst.snd Prod.snd measurable_snd
    (fun z=>m z.1.1 z.1.2 z.2) hm e he

theorem point_of_active (c e : Domain→ℝ) (k : ℕ) (q : ℝ)
    (m : WordRecursion.State (n+k)) (p : History X k) (hq : q<(carrier L k).terminal p) :
    point L c e k q m p=FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
      (fullResidualCovariance L c k p q) e
      (stoppedRow (stops L k p) (targets L k p) (centers L k p)) (oldAverage L c k p) m := by
  simp only [point,if_pos hq]

/-- Genuine joint Borel old-space averaging; original old times and the
current lower cutoff may themselves vary with the outer parameters. -/
theorem spatial_variable_measurable (c : Domain→ℝ) (hc : Measurable c) (k : ℕ)
    (root : W→X) (hroot : Measurable root) (times : W→Fin k→ℝ) (htimes : Measurable times)
    (q : W→ℝ) (hq : Measurable q)
    (m : W×History X k→WordRecursion.State (n+k)) (hm : Measurable m)
    (e : (W×History X k)×Domain→ℝ) (he : Measurable e) :
    Measurable (fun w=>∫ x : Fin k→HeatCircle,
      point L c (fun r=>e ((w,separated k (root w,times w,x)),r)) k (q w)
        (m (w,separated k (root w,times w,x))) (separated k (root w,times w,x))
          ∂Measure.pi (fun _=>haarAddCircle)) := by
  let h : W×(Fin k→HeatCircle)→History X k := fun z=>separated k (root z.1,times z.1,z.2)
  have hh : Measurable h := (separated_measurable k).comp
    ((hroot.comp measurable_fst).prodMk ((htimes.comp measurable_fst).prodMk measurable_snd))
  have hm' : Measurable (fun z : W×(Fin k→HeatCircle)=>m (z.1,h z)) := by
    convert! hm.comp (measurable_fst.prodMk hh) using 1
  have he' : Measurable (fun z : (W×(Fin k→HeatCircle))×Domain=>e ((z.1.1,h z.1),z.2)) := by
    convert! he.comp ((measurable_fst.fst.prodMk (hh.comp measurable_fst)).prodMk measurable_snd) using 1
  have hp := point_variable_measurable L c hc k h hh (fun z=>q z.1) (hq.comp measurable_fst)
    (fun z=>m (z.1,h z)) hm' (fun z=>e ((z.1.1,h z.1),z.2)) he'
  convert! (hp.stronglyMeasurable.integral_prod_right'
    (ν:=Measure.pi (fun _ : Fin k=>haarAddCircle))).measurable using 1

end SHE.ActualCovarianceMarkFields
