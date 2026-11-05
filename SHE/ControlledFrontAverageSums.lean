module

public import SHE.RootHistoryFinite
public import SHE.ControlledFrontRootSums
public import SHE.ControlledFamilyFrontFields
public import SHE.BoundedGaussianSums
public import SHE.UnconditionalCovarianceSums
public import SHE.TranslatedProfileRowEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ControlledFrontAverageSums
open AddCircle
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers SmoothCylinders UniformSmooth PhysicalChainArrays PhysicalScoreChain
  RootSmoothSums CoveredControlledLaw
open scoped NNReal BigOperators
local instance controlledFrontAverageSums_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFrontAverageSums_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFrontAverageSums_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : VariableObservations.Family HeatCircle n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : ℕ→HeatCircle→WordRecursion.State n→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
variable (hFm : ∀ j,Measurable (fun z : HeatCircle×WordRecursion.State n=>F j z.1 z.2))
local notation "B"=>(fun j=>ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop (F j) (hF j) (hFm j))

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (p : Ω→ControlledProfile.Inputs) (hp : Measurable p)
variable (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D)
variable (ν : Measure HeatCircle) [IsFiniteMeasure ν]
local notation "Rzero"=>ControlledReferenceLevel.referenceData P A hA Λ 0 v b hvb (0,0)

include hp hU hD in
/-- Genuine pre-cancellation old-history L1 for an arbitrary Borel
random past/current input, uniform in all current states and theta. -/
theorem active_integrable (j k : ℕ) (q θ : ℝ) :
    Integrable (fun z : Ω×History HeatCircle k=>ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop
      (F j) (hF j) (hFm j) (p z.1) k z.2 q (U z.1) (D z.1) θ)
      (μ.prod (historyMeasure Rzero ν k)) := by
  obtain ⟨K,hK,hbound⟩:=ControlledFamilyFrontFields.actual_value_bound P A hA Λ v b hvb Z htarget hstop
    (F j) (hF j) (hFm j) k
  have hi:=((UncutHistoryMass.weight_integrable (B j (0,(0,0))) ν k).const_mul K).comp_snd μ
  apply hi.mono'
    (ControlledFamilyFrontFields.active_value_measurable P A hA Λ v b hvb Z htarget hstop
      (F j) (hF j) (hFm j) k (fun z : Ω×History HeatCircle k=>p z.1) (hp.comp measurable_fst)
      Prod.snd measurable_snd (fun _=>q) measurable_const
      (fun z=>U z.1) (fun z=>D z.1) (hU.comp measurable_fst) (hD.comp measurable_fst)
      (fun _=>θ) measurable_const).aestronglyMeasurable
  exact ae_of_all _ (fun z=>by
    simp only [Real.norm_eq_abs,ControlledFamilyFrontFields.activeValue]
    split_ifs
    · exact hbound (p z.1) θ z.2 q (U z.1) (D z.1)
    · exact (abs_zero.trans_le (mul_nonneg hK (UncutSmoothWords.weight_nonneg _ _ _))))

def average (G : HeatCircle→WordRecursion.State n→ℝ) (hg : UniformBoundedSmooth G)
    (hgm : Measurable (fun z : HeatCircle×WordRecursion.State n=>G z.1 z.2))
    (k : ℕ) (q θ : ℝ) (z : Ω×HeatCircle) : ℝ:=
  HistoryProductMeasure.rootAverage Rzero k (fun a=>
    ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop G hg hgm
      (p a.1) k a.2 q (U a.1) (D a.1) θ) z

include hp hU hD in
/-- Literal finite-root cutoff equality for the actual Gaussian-front
old-history average, preserving the random inputs and spatial output. -/
theorem average_sum_ae (s : Finset ℕ) (k : ℕ) (q θ : ℝ) :
    average P A hA Λ v b hvb Z htarget hstop p U D
      (rootSum F s) (rootSum_uniform F hF s) (rootSum_measurable F hFm s) k q θ=ᵐ[μ.prod haarAddCircle]
      fun z=>∑ j∈s,average P A hA Λ v b hvb Z htarget hstop p U D
        (F j) (hF j) (hFm j) k q θ z := by
  have he:=HistoryProductMeasure.root_average_finsetSum Rzero k μ
    (fun j a=>ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop
      (F j) (hF j) (hFm j) (p a.1) k a.2 q (U a.1) (D a.1) θ)
    (fun j=>active_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm μ p hp U D hU hD
      haarAddCircle j k q θ) s
  have hpoint : (fun a : Ω×History HeatCircle k=>ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop
      (rootSum F s) (rootSum_uniform F hF s) (rootSum_measurable F hFm s) (p a.1) k a.2 q (U a.1) (D a.1) θ)=
      (fun a=>∑ j∈s,ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop
        (F j) (hF j) (hFm j) (p a.1) k a.2 q (U a.1) (D a.1) θ) :=
    funext (fun a=>ControlledFrontRootSums.activeValue_sum P A hA Λ v b hvb Z htarget hstop F hF hFm
      s (p a.1) k a.2 q (U a.1) (D a.1) θ)
  unfold average
  rw [hpoint]
  exact he

include hp hU hD in
theorem average_integrable (G : HeatCircle→WordRecursion.State n→ℝ) (hg : UniformBoundedSmooth G)
    (hgm : Measurable (fun z : HeatCircle×WordRecursion.State n=>G z.1 z.2))
    (k : ℕ) (q θ : ℝ) :
    Integrable (average P A hA Λ v b hvb Z htarget hstop p U D G hg hgm k q θ)
      (μ.prod haarAddCircle) :=
  HistoryProductMeasure.root_average_integrable Rzero k μ _
    (active_integrable P A hA Λ v b hvb Z htarget hstop (fun _=>G) (fun _=>hg) (fun _=>hgm)
      μ p hp U D hU hD haarAddCircle 0 k q θ)

end SHE.ControlledFrontAverageSums

