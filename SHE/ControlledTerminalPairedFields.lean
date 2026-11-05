module

public import SHE.PairedAssignedFamilyFields
public import SHE.PairedSlotAverages
public import SHE.ControlledThetaCovarianceFields
public import SHE.ControlledFamilyProfileMarkFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.ControlledTerminalPairedFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalScoreChain
  ControlledFamilyProfileForest SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledTerminalPairedFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledTerminalPairedFields_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledTerminalPairedFields_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable {X:Type} [MeasurableSpace X] (Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (Function.uncurry F))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

/-- Literal normalized terminal comparison slot, on the ORIGINAL
physical old laws and full residual at theta zero. Own theta-one and
theta-zero baselines are retained separately. -/
def average (k:ℕ) (p:Inputs) (h:History X k) (newMean oldMean:WordRecursion.State (1+k))
    (choices:List (Fin k×Fin (k+1))) (ν χ:ℝ) (i:Fin (k+1)):ℝ:=
  let L:=Base (0,p)
  let A:=covariances L ((carrier L k).observations.observations h) (oldProfile P Λ v p) k h
  let D:=directions L ((carrier L k).observations.observations h) k h
  let B:=fullResidualCovariance L (oldProfile P Λ v p) k h ((carrier L k).terminal h)
  ∫x,PairedAssignedTelescope.slot P A D choices (F (rootParameter k h))
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) newMean oldMean
    (baseline (Base (1,p)) k h) (baseline L k h) ν χ i x
    ∂(Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (1+k)) (A j))).prod
      (multivariateGaussian (0:WordRecursion.State (1+k)) B)

/-- The ACTUAL terminal normalized slot is jointly Borel in all
original histories, random past data and current endpoint states. This
permits genuine newest-spatial/history Fubini rather than a diagonal
substitution into a fixed-frame exceptional set. -/
theorem average_variable_measurable {W:Type} [MeasurableSpace W] (k:ℕ)
    (p:W→Inputs) (hp:Measurable p) (h:W→History X k) (hh:Measurable h)
    (newMean oldMean:W→WordRecursion.State (1+k)) (hn:Measurable newMean) (ho:Measurable oldMean)
    (choices:List (Fin k×Fin (k+1))) (ν χ:ℝ) (i:Fin (k+1)):
    Measurable (fun w=>average P hA Λ v b hvb Z htarget hstop F hF hFm k (p w) (h w)
      (newMean w) (oldMean w) choices ν χ i) := by
  let par:W→ℝ×Inputs:=fun w=>(0,p w)
  have hpar:Measurable par:=measurable_const.prodMk hp
  let c:W×StoppedGaussianFeatures.Domain→ℝ:=fun z=>oldProfile P Λ v (p z.1) z.2
  have hc:Measurable c:=ControlledFamilyProfileMarkFields.old_profile_variable_measurable P Λ v p hp
  let AA:=fun w=>covariances (Base (par w)) ((carrier (Base (par w)) k).observations.observations (h w))
    (fun z=>c (w,z)) k (h w)
  let DD:=fun w=>directions (Base (par w)) ((carrier (Base (par w)) k).observations.observations (h w)) k (h w)
  let q:=fun w=>(carrier (Base (par w)) k).terminal (h w)
  have hq:Measurable q:=by
    convert! (ControlledThetaWordFields.terminal_joint_measurable
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k).comp (hpar.prodMk hh) using 1
  let BB:=fun w=>fullResidualCovariance (Base (par w)) (fun z=>c (w,z)) k (h w) (q w)
  have hB:Measurable BB:=by
    have hg:=ControlledThetaCovarianceFields.capped_residual_variable_measurable
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k par hpar h hh q hq c hc
    convert! hg using 1
    funext w
    simp only [BB,ActualCovarianceMarkFields.cappedResidual,q,min_self]
  have hbas(a:ℝ)(j:Fin k):Measurable (fun w=>baseline (Base (a,p w)) k (h w) j):=by
    have hl:Measurable (fun w=>lower (Base (0,(0,0))) k (h w) j):=(lower_measurable _ k j).comp hh
    have hs:Measurable (fun w=>space k (h w) j):=(space_measurable k j).comp hh
    have hg:=(ControlledThetaWordFields.coefficient_joint_measurable P Λ v).comp
      (((measurable_const (a:=a)).prodMk hp).prodMk (hl.prodMk hs))
    convert! hg using 1
    funext w
    unfold baseline
    rw [ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
      (a,p w) (0,(0,0)) k (h w)]
    rfl
  have hroot:Measurable (fun z:W×WordRecursion.State 1=>F (rootParameter k (h z.1)) z.2):=
    hFm.comp ((((rootParameter_measurable k).comp hh).comp measurable_fst).prodMk measurable_snd)
  convert! PairedAssignedTelescope.slot_average_family_measurable P AA
    (fun j=>ControlledThetaCovarianceFields.covariances_variable_measurable
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k par hpar h hh c hc j)
    BB hB DD (fun j=>ControlledThetaCovarianceFields.directions_variable_measurable
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm k par hpar h hh j)
    choices (fun w=>F (rootParameter k (h w))) hroot (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i))
    newMean oldMean hn ho (fun w=>baseline (Base (1,p w)) k (h w))
    (fun w=>baseline (Base (0,p w)) k (h w)) (hbas 1) (hbas 0) ν χ i using 1

end SHE.ControlledTerminalPairedFields
