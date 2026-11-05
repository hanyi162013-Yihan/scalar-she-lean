module

public import SHE.ParentMeanMass
public import SHE.ControlledFamilyMeanFields
public import SHE.ConditionalSpatialMoments
public import SHE.FiniteRowFirstMoment
public import SHE.ControlledFamilyKernelBounds

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledFamilyMeanFirstMoment
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianConvolution SmoothCylinders UniformSmooth
  HistoryProductMeasure ActualMeanKernel PhysicalParentGeometry PhysicalScoreChain ScalarMeanEnvelope
open scoped NNReal
local instance controlledFamilyMeanFirstMoment_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyMeanFirstMoment_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyMeanFirstMoment_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State 1=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm
variable {Ω : Type} [MeasurableSpace Ω]
attribute [local irreducible] cappedAverage weightedPoint

/-- An absolute first moment of the literal current-mean derivative at
one original history. Spatial heat mass is integrated before the old
parent density, leaving that density UNSQUARED. -/
theorem first_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Ω→ℝ×Inputs) (ha : Measurable a) (k : ℕ)
    (m : Ω→History X k→WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω×History X k=>m z.1 z.2))
    (q : ℝ) (p : History X k) (hq : q<(CutoffCarriers.carrier (Base (0,(0,0))) k).terminal p)
    (V : Ω→CircleL2) (hV : Measurable V) (hVi : Integrable (fun ω=>‖V ω‖^2) μ)
    (D0 C : ℝ) (hD0 : 0≤D0) (hC : 0≤C)
    (hpoint : ∀ᵐ y ∂haarAddCircle,
      Integrable (fun ω=>|weightedPoint (Base (a ω)) k Λ q q (m ω) p y|^2) μ ∧
      (∫ ω,|weightedPoint (Base (a ω)) k Λ q q (m ω) p y|^2 ∂μ)≤
        C*(D0*ParentMeanDensity.globalDensity (Base (0,(0,0))) k p q y)^2) :
    let Zp:=((CutoffCarriers.carrier (Base (0,(0,0))) k).observations.observations p)
    let M:=fun ω=>fderiv ℝ (cappedAverage (Base (a ω)) k q p) (m ω p)
      (PhysicalMeanRange.dampedDirection (fun i=>(Zp i).stop) (fun i=>(Zp i).target)
        (fun i=>NativeHeatSpan.unitCenter (Zp i).center) q Λ (V ω))
    Integrable M μ ∧ (∫ ω,|M ω| ∂μ)≤
      sqrt (∫ ω,‖V ω‖^2 ∂μ)*
        (sqrt C*D0*((1+k:ℕ):ℝ)*ParentMeanDensity.parentProduct (Base (0,(0,0))) k p) := by
  intro Zp M
  let L0:=Base (0,(0,0))
  let D : Ω→WordRecursion.State (1+k)→L[ℝ]ℝ:=fun ω=>fderiv ℝ (cappedAverage (Base (a ω)) k q p) (m ω p)
  have hm0 : Measurable (fun ω=>m ω p):=hm.comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable (fun ω : Ω=>((a ω,(q,p)),m ω p)):=
    (ha.prodMk (measurable_const.prodMk measurable_const)).prodMk hm0
  have hGrad0:=ControlledThetaBackwardFields.gradient_joint_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k
  have hD : Measurable D:=by
    have hh:=hGrad0.comp hmap
    convert! hh using 1
  have hqall (ω : Ω) : q<(CutoffCarriers.carrier (Base (a ω)) k).terminal p := by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
      (a ω) (0,(0,0)) k p]
    exact hq
  have hr (i : Fin (1+k)) : q<(Zp i).target:=hq.trans_le
    ((CutoffCarriers.carrier L0 k).targets_after p i)
  have he (ω : Ω) (y : HeatCircle) : weightedPoint (Base (a ω)) k Λ q q (m ω) p y=
      D ω (StopWeightedRows.weightedHeatRow Λ Zp q q y) := by
    rw [weightedPoint_of_active _ _ _ _ _ _ _ _ (hqall ω) (hqall ω)]
    dsimp only [D]
    simp only [cappedAverage,min_eq_left (hqall ω).le]
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
      (a ω) (0,(0,0)) k p]
  have hP : Measurable (fun z : HeatCircle×Ω=>D z.2 (StopWeightedRows.weightedHeatRow Λ Zp q q z.1)) := by
    have hh:=ControlledThetaWeightedFields.weightedPoint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
      (fun z : HeatCircle×Ω=>a z.2) (ha.comp measurable_snd)
      (fun _=>p) measurable_const (fun _=>q) (fun _=>q) measurable_const measurable_const
      (fun z=>m z.2 p) (hm0.comp measurable_snd) (fun z=>z.1) measurable_fst
    convert! hh using 1
    funext z
    change D z.2 (StopWeightedRows.weightedHeatRow Λ Zp q q z.1)=
      weightedPoint (Base (a z.2)) k Λ q q (fun _=>m z.2 p) p z.1
    rw [weightedPoint_of_active _ _ _ _ _ _ _ _ (hqall z.2) (hqall z.2)]
    dsimp only [D]
    simp only [cappedAverage,min_eq_left (hqall z.2).le]
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
      (a z.2) (0,(0,0)) k p]
  let B : HeatCircle→ℝ:=fun y=>C*(D0*ParentMeanDensity.globalDensity L0 k p q y)^2
  have hmass:=ParentMeanDensity.globalDensity_square_mass L0 k p hq
  have heq : B=fun y=>(C*D0^2)*ParentMeanDensity.globalDensity L0 k p q y^2:=by
    funext y
    dsimp only [B]
    ring
  have hBi : Integrable B haarAddCircle:=by
    rw [heq]
    exact hmass.1.const_mul (C*D0^2)
  have hs : ∀ᵐ y ∂haarAddCircle,
      Integrable (fun ω=>|D ω (StopWeightedRows.weightedHeatRow Λ Zp q q y)|^2) μ ∧
      (∫ ω,|D ω (StopWeightedRows.weightedHeatRow Λ Zp q q y)|^2 ∂μ)≤B y := by
    filter_upwards [hpoint] with y hy
    have hef : (fun ω=>|weightedPoint (Base (a ω)) k Λ q q (m ω) p y|^2)=
        (fun ω=>|D ω (StopWeightedRows.weightedHeatRow Λ Zp q q y)|^2):=
      funext (fun ω=>by rw [he])
    rw [hef] at hy
    exact hy
  have hK:=StopWeightedRows.kernel_second_moment μ D hD Λ Zp q q hr hP B hBi hs
  have hn : 0≤ParentMeanDensity.parentProduct L0 k p:=ParentMeanDensity.parentProduct_nonneg L0 k p
  let K:=sqrt C*D0*((1+k:ℕ):ℝ)*ParentMeanDensity.parentProduct L0 k p
  have hKn : 0≤K:=mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) hD0) (Nat.cast_nonneg _)) hn
  have hKbound : (∫ ω,‖StopWeightedRows.kernel (D ω) Λ Zp q q‖^2 ∂μ)≤K^2 := by
    apply hK.2.trans
    rw [heq,integral_const_mul]
    have hb:=mul_le_mul_of_nonneg_left hmass.2 (mul_nonneg hC (sq_nonneg D0))
    have hk : K^2=C*D0^2*(((1+k:ℕ):ℝ)^2*ParentMeanDensity.parentProduct L0 k p^2):=by
      dsimp only [K]
      rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hC]
      ring
    rw [hk]
    exact hb
  exact StopWeightedRows.input_first_moment μ D hD Λ Zp q hr V hV hVi hK.1 K hKn hKbound

end SHE.ControlledFamilyMeanFirstMoment
