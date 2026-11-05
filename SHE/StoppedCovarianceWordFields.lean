module

public import SHE.VariableGaussianWordMarks
public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.StoppedCovarianceWordFields
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement GaussianWordAffine VariableGaussianWordMarks NativeOldRoot
  MeasurableGaussianScores GaussianScoreKernel
open scoped NNReal InnerProductSpace
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {n:ℕ}

def translatedObservations (σ target:Fin n→ℝ)(center:Fin n→HeatCircle):
    VariableObservations.Family HeatCircle n where
  observations x i:=⟨σ i,target i,center i+x⟩
  stop_measurable _:=measurable_const
  target_measurable _:=measurable_const
  center_measurable _:=measurable_const.add measurable_id

def covarianceField (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(c:Domain→ℝ)(x:HeatCircle):
    Matrix (Fin n) (Fin n) ℝ:=stoppedCovariance σ target (fun i=>center i+x) c 0

def rowField (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(p:HeatCircle×Domain):State n:=
  stoppedRow σ target (fun i=>center i+p.1) p.2

theorem covarianceField_measurable (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (c:Domain→ℝ)(hc:Measurable c):Measurable (covarianceField σ target center c):=
  StoppedGaussianFields.covariance_measurable (translatedObservations σ target center)
    (hc.comp measurable_snd) measurable_const

theorem rowField_measurable (σ target:Fin n→ℝ)(center:Fin n→HeatCircle):
    Measurable (rowField σ target center):=
  StoppedGaussianFields.row_measurable (translatedObservations σ target center)

def scoreInput (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(c e:Domain→ℝ)(x:HeatCircle):ℝ:=
  ∫p,|e p| *scoreVariance (covarianceField σ target center c x)
    (rowField σ target center (x,p)) ∂historyMeasure 0

theorem scoreInput_measurable (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (c e:Domain→ℝ)(hc:Measurable c)(he:Measurable e):Measurable (scoreInput σ target center c e):=by
  have hS:Measurable (fun p:HeatCircle×Domain=>scoreVariance (covarianceField σ target center c p.1)
      (rowField σ target center p)):=by
    have hA:=covarianceField_measurable σ target center c hc
    have hD:=rowField_measurable σ target center
    convert! (scoreVariance_measurable (n:=n)).comp
      ((hA.comp (measurable_fst:Measurable (Prod.fst:HeatCircle×Domain→HeatCircle))).prodMk hD) using 1
  exact ((((continuous_abs.measurable.comp he).comp measurable_snd).mul hS).stronglyMeasurable.integral_prod_right').measurable

def covarianceWordField (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(c e:Domain→ℝ)
    (v:ℝ≥0)(f a:ℝ→ℝ)(K L:State n→L[ℝ] ℝ)(m:HeatCircle→State n)(x:HeatCircle):ℝ:=
  covarianceMark (historyMeasure 0) (covarianceField σ target center c x) e
    (fun p=>rowField σ target center (x,p))
    (fun y=>oldRoot v f (K y)) (fun y=>a (L y)) (m x)

theorem covarianceWordField_measurable (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (c e:Domain→ℝ)(hc:Measurable c)(he:Measurable e)
    (v:ℝ≥0)(f a:ℝ→ℝ)(hf:Measurable f)(ha:Measurable a)(K L:State n→L[ℝ] ℝ)
    (m:HeatCircle→State n)(hm:Measurable m):Measurable (covarianceWordField σ target center c e v f a K L m):=
  covarianceMark_variable_variance_measurable (historyMeasure 0)
    (covarianceField σ target center c) (covarianceField_measurable σ target center c hc)
    m hm (fun _=>v) measurable_const (fun p=>e p.2) (he.comp measurable_snd)
    (rowField σ target center) (rowField_measurable σ target center) f a hf ha K L

end SHE.StoppedCovarianceWordFields
