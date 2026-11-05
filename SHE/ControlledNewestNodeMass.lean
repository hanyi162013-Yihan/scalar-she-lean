module
public import SHE.ControlledNewestHessianBound
public import SHE.PhysicalInsertion
public import SHE.PhysicalRemainderBound
public import SHE.PhysicalParentGeometry
public import SHE.GaussianSmooth
public import SHE.NormalizedInsertion
public import SHE.GaussianConvolution
public import SHE.CutoffWeightedDerivatives

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.ControlledNewestNodeMass
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
open scoped NNReal
local instance controlledNewestNodeMass_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledNewestNodeMass_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledNewestNodeMass_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)
variable (Λ θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {X:Type}[MeasurableSpace X]{n:ℕ}(Z:VariableObservations.Family X n)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State n=>F z.1 z.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm

open AddCircle

/-- Coarse absolute spatial domination by the TRUE successor history
weight. This is only an integrability/Fubini bound at a fixed smooth
index; it is separate from the derivative-free small-error estimate. -/
theorem bound (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)(k:ℕ):
    ∃C:ℝ,0≤C ∧∀(p:Inputs)(h:History X k)(q:ℝ),(v:ℝ)<q→q<(carrier (Base (0,0)) k).terminal h→
      ∀(z:WordRecursion.State (n+k))(ε:ℝ),0≤ε→∀f:HeatCircle→ℝ,Measurable f→(∀y,|f y|≤ε)→
      let G:=gaussianAverage
        (WordRecursion.covariance (referenceData P A hA Λ θ v b hvb p).reference
          ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)
      Integrable (fun y=>f y*WordRecursion.directionalSecond G z
        (heatRow ((carrier (Base p) k).observations.observations h) q y)) haarAddCircle ∧
      |(1/2:ℝ)*∫y,f y*WordRecursion.directionalSecond G z
        (heatRow ((carrier (Base p) k).observations.observations h) q y) ∂haarAddCircle|≤
      C*ε*(∫y,UncutSmoothWords.weight (Base (0,0)) (k+1) (h,(q,y)) ∂haarAddCircle):=by
  obtain ⟨B,hB,hBb⟩:=ControlledNewestHessianBound.bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm k
  refine ⟨B/2,div_nonneg hB (by norm_num),?_⟩
  intro p h q hvq hqt z ε hε f hf hfcap
  dsimp only
  let ZZ:=((carrier (Base p) k).observations.observations h)
  let G:=gaussianAverage
    (WordRecursion.covariance (referenceData P A hA Λ θ v b hvb p).reference ZZ q ((carrier (Base p) k).terminal h))
    (UncutSmoothWords.test (Base p) k h)
  let HH:=WordRecursion.hessian G z
  let W:=UncutSmoothWords.weight (Base (0,0)) k h
  have hW:0≤W:=UncutSmoothWords.weight_nonneg _ _ _
  have hT:(carrier (Base p) k).terminal h=(carrier (Base (0,0)) k).terminal h:=
    ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h
  have hqtp:q<(carrier (Base p) k).terminal h:=by rw [hT];exact hqt
  have hgap:∀i,(carrier (Base p) k).terminal h≤(ZZ i).target:=fun i=>
    ((carrier (Base p) k).stops_after h i).trans
      (RecursiveScoreSupport.carrier_ages (Base p) hages k h i)
  have hi:=PhysicalInsertion.weighted_generator_integrable (fun r:ℝ×HeatCircle=>f r.2)
    (hf.comp measurable_snd) ZZ hε hqtp hgap hfcap HH
  have hr:=PhysicalRemainderBound.row_norm_square_integrable ZZ (fun i=>hqtp.trans_le (hgap i))
  have hHb:‖HH‖≤B*W:=hBb p h q z
  have hrow(y:HeatCircle):UncutSmoothWords.weight (Base (0,0)) (k+1) (h,(q,y))=
      W*‖heatRow ZZ q y‖^2:=by
    change W*‖CutoffCarriers.row (Base (0,0)) k (h,(q,y))‖^2=_
    have hint:CutoffCarriers.Interior (Base (0,0)) k (h,(q,y)):=⟨hvq,hqt⟩
    rw [CutoffCarriers.row,if_pos hint]
    rw [ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm (0,0) p k h]
    have htime:(carrier (Base (0,0)) k).nodeTime (h,(q,y))=q:=
      ClippedCovariance.clip_eq ⟨hvq.le,hqt.le⟩
    rw [htime]
  have hpoint(y:HeatCircle):‖f y*HH (heatRow ZZ q y) (heatRow ZZ q y)‖≤
      ε*B*UncutSmoothWords.weight (Base (0,0)) (k+1) (h,(q,y)):=by
    have hb:‖HH (heatRow ZZ q y) (heatRow ZZ q y)‖≤B*W*‖heatRow ZZ q y‖*‖heatRow ZZ q y‖:=
      (GaussianTaylor.bilinear_norm_le HH _ _).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHb (norm_nonneg _)) (norm_nonneg _))
    rw [norm_mul,Real.norm_eq_abs]
    have ht:=mul_le_mul (hfcap y) hb (norm_nonneg _) hε
    exact ht.trans_eq (by rw [hrow];ring)
  have hw:Integrable (fun y=>UncutSmoothWords.weight (Base (0,0)) (k+1) (h,(q,y))) haarAddCircle:=by
    simpa only [hrow] using hr.const_mul W
  have hb:=norm_integral_le_of_norm_le (hw.const_mul (ε*B)) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hb
  refine ⟨hi,?_⟩
  rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<1/2)]
  have ht:=mul_le_mul_of_nonneg_left hb (by norm_num:(0:ℝ)≤1/2)
  convert! ht using 1 <;> (try simp only [Real.norm_eq_abs,WordRecursion.directionalSecond]) <;> (try dsimp only [HH,G,ZZ]) <;> ring

end SHE.ControlledNewestNodeMass
