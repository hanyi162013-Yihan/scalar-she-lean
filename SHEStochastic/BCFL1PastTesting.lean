module

public import SHEStochastic.BCFPastTesting
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.BCFL1PastTesting
open MeasureTheory
open scoped NNReal ENNReal
variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → X) (hZ : Measurable Z)

include hZ in
/-- Bounded continuous past tests determine integrable increments.
Reweighting by 1+|Y| reduces the claim to the existing L2 density proof;
no new approximation argument or second moment of Y is needed. -/
theorem setIntegral_zero (Y : Ω → ℝ) (hY : Integrable Y μ)
    (htest : ∀ f : BoundedContinuousFunction X ℝ,(∫ ω,f (Z ω)*Y ω ∂μ)=0)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.comap Z inferInstance] A) :
    (∫ ω in A,Y ω ∂μ)=0 := by
  let w := fun ω => 1+|Y ω|
  let S := fun ω => Y ω/w ω
  let ν := μ.withDensity (fun ω => ENNReal.ofReal (w ω))
  have hwpos (ω : Ω) : 0<w ω := by dsimp only [w];positivity
  have hwi : Integrable w μ := (integrable_const (1 : ℝ)).add hY.norm
  have hwm : AEMeasurable (fun ω => ENNReal.ofReal (w ω)) μ := hwi.aemeasurable.ennreal_ofReal
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hwi.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => (hwpos ω).le))).mpr hwi)
  have hS : MemLp S 2 ν := MemLp.of_bound
    ((hY.aestronglyMeasurable.div₀ hwi.aestronglyMeasurable).mono_ac (withDensity_absolutelyContinuous μ _))
    1 (Filter.Eventually.of_forall (fun ω => by
      change ‖Y ω/w ω‖≤1
      rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (hwpos ω),div_le_one (hwpos ω)]
      dsimp only [w]
      linarith))
  have hmul (ω : Ω) : w ω*S ω=Y ω := by
    dsimp only [S]
    field_simp [(hwpos ω).ne']
  have htests (f : BoundedContinuousFunction X ℝ) : (∫ ω,f (Z ω)*S ω ∂ν)=0 := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hwm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    have he : (fun ω => (ENNReal.ofReal (w ω)).toReal • (f (Z ω)*S ω))=
        (fun ω => f (Z ω)*Y ω) := by
      funext ω
      rw [ENNReal.toReal_ofReal (hwpos ω).le,smul_eq_mul,←mul_assoc,
        mul_comm (w ω) (f (Z ω)),mul_assoc,hmul ω]
    rw [he]
    exact htest f
  have hz := BCFPastTesting.setIntegral_zero ν Z hZ S hS htests hA
  have hAmbient : MeasurableSet A := hZ.comap_le A hA
  have he : (∫ ω in A,S ω ∂ν)=(∫ ω in A,Y ω ∂μ) := by
    change (∫ ω,S ω ∂(μ.withDensity (fun ω => ENNReal.ofReal (w ω))).restrict A)=_
    rw [restrict_withDensity hAmbient,
      integral_withDensity_eq_integral_toReal_smul₀ hwm.restrict
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      change (ENNReal.ofReal (w ω)).toReal • S ω=Y ω
      rw [ENNReal.toReal_ofReal (hwpos ω).le,smul_eq_mul,hmul ω]
  exact he.symm.trans hz

include hZ in
/-- The same determining tests give a zero conditional expectation
under a first-moment assumption alone. -/
theorem condExp_zero (Y : Ω → ℝ) (hY : Integrable Y μ)
    (htest : ∀ f : BoundedContinuousFunction X ℝ,(∫ ω,f (Z ω)*Y ω ∂μ)=0) :
    μ[Y | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun _ => (0 : ℝ) := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hZ.comap_le hY
    (fun _ _ _ => (integrable_const (0 : ℝ)).integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  rw [integral_zero]
  exact (setIntegral_zero μ Z hZ Y hY htest hA).symm

theorem martingale {T : Type*} [Preorder T]
    (F : Filtration T (inferInstance : MeasurableSpace Ω)) (past : T → Ω → X)
    (hpast : ∀ t,Measurable (past t))
    (hF : ∀ t,F t≤MeasurableSpace.comap (past t) inferInstance)
    (M : T → Ω → ℝ) (ha : StronglyAdapted F M) (hM : ∀ t,Integrable (M t) μ)
    (htest : ∀ s t,s≤t → ∀ f : BoundedContinuousFunction X ℝ,
      (∫ ω,f (past s ω)*(M t ω-M s ω) ∂μ)=0) :
    Martingale M F μ := by
  refine ⟨ha,fun s t hst => ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hM t)
    (fun _ _ _ => (hM s).integrableOn) (fun A hA _ => ?_) (ha s).aestronglyMeasurable).symm
  have hz := setIntegral_zero μ (past s) (hpast s) (fun ω => M t ω-M s ω)
    ((hM t).sub (hM s)) (htest s t hst) (hF s A hA)
  rw [integral_sub (hM t).integrableOn (hM s).integrableOn] at hz
  exact (sub_eq_zero.mp hz).symm

end SHEStochastic.BCFL1PastTesting
