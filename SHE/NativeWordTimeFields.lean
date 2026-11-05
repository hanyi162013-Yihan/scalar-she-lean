module

public import SHE.NativeHeatFields
public import SHE.RootCornerTransfer
public import SHE.NativeMeanWordDomination

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

/-! Jointly Borel actual first-word mean fields at all intermediate times,
including varying old fraction, full native covariance, and physical means. -/
namespace SHE.NativeWordTimeFields
open Set MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore HeatHistoryScore HeatTorus HeatTorusKernel GaussianGramScore GaussianIncrement
  MeasurableGaussianScores NativeMeanFields NativeMeanScoreKernel MeasurableGeneralizedInverse
  GaussianWordFields NativeGaussianFirstWord GaussianAudit NativeOldRoot NativeFirstWordMeanTree
  NativeFirstWordMeanPower GaussianWordMeanDerivative NativeMeanPointBound NativeMeanWordDomination
  ProfileVariance OldFractionHeatScale FirstWordPowers ProfileL2 StoppedGaussianMarginals
  HeatTreeAveraging NativeHeatFields VariableOldGaussian
open scoped InnerProductSpace NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

abbrev Parameter:=ℝ×(UnitAddCircle×UnitAddCircle)

def targets (h s:ℝ)(i:Fin 2):ℝ:=if i=0 then h else s

theorem targets_measurable (h:ℝ)(i:Fin 2):Measurable (fun s=>targets h s i):=by
  classical
  by_cases hi:i=0 <;> simp only[targets,hi,ite_true,ite_false] <;> fun_prop

def timeObservations (h:ℝ):VariableObservations.Family Parameter 2 where
  observations p i:=⟨targets h p.1 i,targets h p.1 i,
    nativeCenter (fun j=>NativeFirstWordMeanTree.relativeCenters p.2.1 j+p.2.2) i⟩
  stop_measurable i:=(targets_measurable h i).comp measurable_fst
  target_measurable i:=(targets_measurable h i).comp measurable_fst
  center_measurable i:=(CircleNormalization.continuous_scale 1 (2*π)).measurable.comp
    (((NativeFirstWordMeanTree.relativeCenters_measurable i).comp measurable_snd.fst).add measurable_snd.snd)

def covariance (h:ℝ)(c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(p:Parameter):Mat 2:=
  StoppedGaussianFeatures.stoppedCovariance (targets h p.1) (targets h p.1)
    (nativeCenter (fun i=>NativeFirstWordMeanTree.relativeCenters p.2.1 i+p.2.2))
    (fun z=>c (p.1,(p.2,z))) 0

def direction (h Λ:ℝ)(d:HeatTorus.CircleL2)(p:Parameter):State 2:=
  physicalDirection (targets h p.1) (fun i=>NativeFirstWordMeanTree.relativeCenters p.2.1 i+p.2.2) Λ d

def gaussianMeanWord (h Λ ellOld:ℝ)(d:HeatTorus.CircleL2)
    (c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(m:Parameter→State 2)
    (f b:ℝ→ℝ)(p:Parameter):ℝ:=
  firstMeanScore (covariance h c p) (direction h Λ d p) (positiveOldVariance ellOld (h-p.1))
    f b (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) (m p)

def heatMeanWord (h Λ ellOld:ℝ)(d:HeatTorus.CircleL2)
    (c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(m:Parameter→State 2)
    (f b:ℝ→ℝ)(p:ℝ×UnitAddCircle):ℝ:=
  ∫y,‖physicalEdge (h-p.1) y‖^2*gaussianMeanWord h Λ ellOld d c m f b (p.1,(y,p.2)) ∂haarAddCircle

theorem covariance_measurable (h:ℝ)(c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(hc:Measurable c):
    Measurable (covariance h c):=by
  have hm:Measurable (fun p:Parameter×Domain=>c (p.1.1,(p.1.2,p.2))):=
    hc.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact StoppedGaussianFields.covariance_measurable (timeObservations h) hm measurable_const

theorem direction_measurable (h Λ:ℝ)(d:HeatTorus.CircleL2):Measurable (direction h Λ d):=
  physicalDirection_measurable (fun p:Parameter=>targets h p.1)
    (fun i=>(targets_measurable h i).comp measurable_fst)
    (fun p i=>NativeFirstWordMeanTree.relativeCenters p.2.1 i+p.2.2)
    (fun i=>((NativeFirstWordMeanTree.relativeCenters_measurable i).comp measurable_snd.fst).add measurable_snd.snd) Λ d

theorem gaussianMeanWord_measurable (h Λ ellOld:ℝ)(d:HeatTorus.CircleL2)
    (c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(hc:Measurable c)
    (m:Parameter→State 2)(hm:Measurable m)(f b:ℝ→ℝ)(hf:Measurable f)(hb:Measurable b):
    Measurable (gaussianMeanWord h Λ ellOld d c m f b):=
  firstMeanScore_variable_variance_measurable (covariance h c) (covariance_measurable h c hc)
    (direction h Λ d) m (direction_measurable h Λ d) hm
    (fun p=>positiveOldVariance ellOld (h-p.1))
    ((positiveOldVariance_measurable ellOld).comp (measurable_const.sub measurable_fst))
    f b hf hb (EuclideanSpace.proj 0) (EuclideanSpace.proj 1)

theorem heatMeanWord_measurable (h Λ ellOld:ℝ)(d:HeatTorus.CircleL2)
    (c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(hc:Measurable c)
    (m:Parameter→State 2)(hm:Measurable m)(f b:ℝ→ℝ)(hf:Measurable f)(hb:Measurable b):
    Measurable (heatMeanWord h Λ ellOld d c m f b):=by
  have hK:Measurable (fun p:(ℝ×UnitAddCircle)×UnitAddCircle=>physicalEdge (h-p.1.1) p.2):=
    physicalEdge_measurable.comp ((measurable_const.sub measurable_fst.fst).prodMk measurable_snd)
  have hW:= (gaussianMeanWord_measurable h Λ ellOld d c hc m hm f b hf hb).comp
    (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
  exact (((hK.norm.pow_const 2).mul hW).stronglyMeasurable.integral_prod_right' (ν:=haarAddCircle)).measurable

/-- At positive intermediate times, the Borel field is exactly the literal
heat-tree derivative already estimated, with its old physical variance. -/
theorem heatMeanWord_eq {h s:ℝ}(hs:0<s)(hsh:s<h)(Λ ellOld:ℝ)(d:HeatTorus.CircleL2)
    (c:ℝ×((UnitAddCircle×UnitAddCircle)×Domain)→ℝ)(m:Parameter→State 2)(f b:ℝ→ℝ)(x:UnitAddCircle):
    let target:=targets h s
    let t:=fun i=>target i/(4*π^2)
    let hage:∀i,target i=4*π^2*t i:=fun i=>by dsimp[t];field_simp
    let act:∀i,0<target i:=fun i=>by
      classical
      by_cases hi:i=0 <;> simp only[target,targets,hi,ite_true,ite_false] <;> linarith
    heatMeanWord h Λ ellOld d c m f b (s,x)=
      ∫y,‖HeatMarkov.kernel ((h-s)/(4*π^2)) (by positivity) y‖^2*
        meanDerivativeField target Λ t hage act (fun p=>c (s,p)) d (fun p=>m (s,p))
          (oldVariance ellOld (h-s)) f b (y,x) ∂haarAddCircle:=by
  intro target t hage act
  apply integral_congr_ae
  filter_upwards[physicalEdge_ae_kernel (sub_pos.mpr hsh)] with y hy
  rw[hy]
  have ht:∀i,0<t i:=fun i=>div_pos (act i) (by positivity)
  have hD:=physicalDirection_eq target (fun i=>NativeFirstWordMeanTree.relativeCenters y i+x) Λ t ht hage act d
  change ‖HeatMarkov.kernel ((h-s)/(4*π^2)) _ y‖^2*
      firstMeanScore _ (physicalDirection target _ Λ d) (positiveOldVariance ellOld (h-s)) f b _ _ _ = _
  rw[hD,positiveOldVariance_eq ellOld (sub_pos.mpr hsh).le]
  rfl

end SHE.NativeWordTimeFields
