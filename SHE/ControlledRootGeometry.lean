module

public import SHE.RootPhysicalGeometry
public import SHE.ControlledFamilyLegFubini

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ControlledRootGeometry
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders UniformSmooth PhysicalChainArrays
open scoped NNReal BigOperators
local instance controlledRootGeometry_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledRootGeometry_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledRootGeometry_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F G : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F) (hG : UniformBoundedSmooth G)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
variable (hGm : Measurable (fun z : X×WordRecursion.State n=>G z.1 z.2))
local notation "LF"=>ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LG"=>ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop G hG hGm

theorem observations_eq (a : ℝ×Inputs) (k : ℕ) (h : History X k) :
    (carrier (LF a) k).observations.observations h=(carrier (LG a) k).observations.observations h :=
  RootFiniteGeometry.observations_eq (LG a) F hF hFm k h

theorem terminal_eq (a : ℝ×Inputs) (k : ℕ) (h : History X k) :
    (carrier (LF a) k).terminal h=(carrier (LG a) k).terminal h :=
  RootFiniteGeometry.terminal_eq (LG a) F hF hFm k h

theorem sigma_eq : ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm=
    ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop G hG hGm := by
  funext p k h i
  unfold ControlledFamilyThreeLeg.sigma
  rw [observations_eq P A hA Λ v b hvb Z htarget hstop F G hF hG hFm hGm]

theorem target_eq : ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm=
    ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop G hG hGm := by
  funext p k h i
  unfold ControlledFamilyThreeLeg.target
  rw [observations_eq P A hA Λ v b hvb Z htarget hstop F G hF hG hFm hGm]

theorem center_eq : ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm=
    ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop G hG hGm := by
  funext p k h i
  unfold ControlledFamilyThreeLeg.center
  rw [observations_eq P A hA Λ v b hvb Z htarget hstop F G hF hG hFm hGm]

/-- The genuine original-stop joint current is independent of the root
test, simultaneously in all past/current inputs and interpolation. -/
theorem mean_eq : ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm=
    ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop G hG hGm := by
  funext p k h q U D θ
  unfold ControlledFamilyActualTransfer.mean
  rw [observations_eq P A hA Λ v b hvb Z htarget hstop F G hF hG hFm hGm,
    center_eq P A hA Λ v b hvb Z htarget hstop F G hF hG hFm hGm]

theorem leafPoint_eq : ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm=
    ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop G hG hGm := by
  funext p k h j
  unfold ControlledFamilyThreeLeg.leafPoint ControlledFamilyThreeLeg.lo
  have he:=RootPhysicalGeometry.lower_eq (LG (0,p)) F hF hFm k h
  change lower (LF (0,p)) k h=lower (LG (0,p)) k h at he
  rw [he]
end SHE.ControlledRootGeometry
