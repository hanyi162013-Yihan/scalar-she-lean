module
public import SHE.ScalarHaarHeatRows
public import SHE.NativeHeatConvolution
public import SHE.CoefficientFields
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.OriginalScalarInputContinuity
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle
open scoped ENNReal Topology
local instance inputContinuity_unit : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance inputContinuity_native : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance inputContinuity_realSigma : MeasurableSpace RealL2 := borel _
local instance inputContinuity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance inputContinuity_circleSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance inputContinuity_circleBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
variable (D : SmoothApproximation.ScalarData)

theorem coefficientMeasurable : Measurable D.coefficient :=
  (ScalarReduction.holder_continuous D.exponent_pos D.holder_nonneg D.holder_bound).measurable

def coefficient (u : RealL2) : RealL2 :=
  realPart (CoefficientFields.coefficient D.coefficient (coefficientMeasurable D) D.upper
    (fun z=>(D.bounds z).2) u)

theorem coefficient_continuous : Continuous (coefficient D) :=
  (Complex.reCLM.compLpL 2 haarAddCircle).continuous.comp
    (CoefficientFields.coefficient_continuous D.exponent_pos D.holder_nonneg D.coefficient
      (coefficientMeasurable D) (fun z=>(D.bounds z).2) D.holder_bound)

theorem coefficient_ae (u : RealL2) : coefficient D u=ᵐ[haarAddCircle] ScalarHaarRotation.scalar D u := by
  filter_upwards [Complex.reCLM.coeFn_compLp
      (CoefficientFields.coefficient D.coefficient (coefficientMeasurable D) D.upper
        (fun z=>(D.bounds z).2) u),
    CoefficientFields.coefficient_ae D.coefficient (coefficientMeasurable D) D.upper
      (fun z=>(D.bounds z).2) u,
    PredictableScalarField.unitField_ae (fun u:RealL2=>u) u] with y hr hc hu
  change coefficient D u y=(_ : ℝ) at hr
  rw [hr,hc]
  change D.coefficient (u y)=D.coefficient (PredictableScalarField.unitField (fun u:RealL2=>u) (u,y))
  rw [hu]

def input (u v : RealL2) : RealL2 :=
  ScalarSplittingInputs.originalInput haarAddCircle (ScalarHaarRotation.scalar D u)
    (ScalarHaarRotation.scalar_measurable D u) D.upper (ScalarHaarRotation.scalar_bound D u) v

theorem input_ae (u v : RealL2) :
    input D u v=ᵐ[haarAddCircle] fun y=>ScalarHaarRotation.scalar D u y*v y :=
  RealMultiplier.operator_ae _ _ _ _ _ _

/-- For a bounded spatial test, the original nonlinear input is a
fixed bounded linear multiplier of the actual continuous g(U) field. -/
theorem input_eq (v : RealL2) (K : ℝ) (hb : ∀ᵐy∂haarAddCircle,‖v y‖≤K) (u : RealL2) :
    input D u v=RealMultiplier.operator haarAddCircle v (Lp.aestronglyMeasurable v) K hb (coefficient D u) := by
  apply Lp.ext
  filter_upwards [input_ae D u v,coefficient_ae D u,
    RealMultiplier.operator_ae haarAddCircle v (Lp.aestronglyMeasurable v) K hb (coefficient D u)] with y hi hc hm
  rw [hi,hm,hc,mul_comm]

theorem input_continuous (v : RealL2) (K : ℝ) (hb : ∀ᵐy∂haarAddCircle,‖v y‖≤K) :
    Continuous (fun u=>input D u v) := by
  have he : (fun u=>input D u v)=(fun u=>RealMultiplier.operator haarAddCircle v
      (Lp.aestronglyMeasurable v) K hb (coefficient D u)) := funext (input_eq D v K hb)
  rw [he]
  exact (RealMultiplier.operator haarAddCircle v (Lp.aestronglyMeasurable v) K hb).continuous.comp
    (coefficient_continuous D)

/-- Positive native heat tests possess a literal finite spatial bound. -/
theorem heat_test_bound {τ : ℝ} (hτ : 0<τ) (x : StoppedFourier.HeatCircle) :
    ∀ᵐy∂haarAddCircle,‖ScalarHaarHeatRows.test τ x y‖≤‖NativeHeatSpan.kernel τ hτ x‖ := by
  have hn : ∀ᵐz∂haarAddCircle (T:=2*Real.pi),
      ‖StoppedFourier.circleHeat τ x z‖≤‖NativeHeatSpan.kernel τ hτ x‖ := by
    filter_upwards [ProfileVariance.heatPhysical_ae hτ x] with z hz
    rw [←hz,←NativeHeatSpan.kernel_eq_physical hτ]
    exact (NativeHeatSpan.kernel τ hτ x).norm_coe_le_norm z
  have hu := CircleNormalization.push_symm_ae_property (StoppedFourier.circleHeat τ x)
    (fun z:ℂ=>‖z‖≤‖NativeHeatSpan.kernel τ hτ x‖) hn
  filter_upwards [hu,Complex.reCLM.coeFn_compLp
    (CircleNormalization.push.symm (StoppedFourier.circleHeat τ x))] with y hy hr
  change ScalarHaarHeatRows.test τ x y=(_ : ℝ) at hr
  rw [hr,Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans hy

theorem heat_input_continuous {τ : ℝ} (hτ : 0<τ) (x : StoppedFourier.HeatCircle) :
    Continuous (fun u=>input D u (ScalarHaarHeatRows.test τ x)) :=
  input_continuous D _ _ (heat_test_bound hτ x)

theorem input_sub (u v w : RealL2) :
    input D u (v-w)=input D u v-input D u w := by
  simp only [input,ScalarSplittingInputs.originalInput,map_sub]

theorem input_norm_le (u v : RealL2) : ‖input D u v‖≤D.upper*‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [input_ae D u v,ScalarHaarRotation.scalar_bound D u] with y hi hb
  rw [hi,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- The test may vary simultaneously with the state. Uniform boundedness
of g controls that variation; only the LIMIT test needs a spatial bound. -/
theorem input_tendsto {α : Type*} {l : Filter α} (u v : α→RealL2) (u₀ v₀ : RealL2)
    (hu : Filter.Tendsto u l (𝓝 u₀)) (hv : Filter.Tendsto v l (𝓝 v₀))
    (K : ℝ) (hb : ∀ᵐy∂haarAddCircle,‖v₀ y‖≤K) :
    Filter.Tendsto (fun a=>input D (u a) (v a)) l (𝓝 (input D u₀ v₀)) := by
  have hv0 : Filter.Tendsto (fun a=>D.upper*‖v a-v₀‖) l (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero,mul_zero] using (hv.sub_const v₀).norm.const_mul D.upper
  have hd : Filter.Tendsto (fun a=>‖input D (u a) (v a)-input D (u a) v₀‖) l (𝓝 (0:ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv0
    · intro a
      exact norm_nonneg _
    · intro a
      change ‖input D (u a) (v a)-input D (u a) v₀‖≤D.upper*‖v a-v₀‖
      rw [←input_sub]
      exact input_norm_le D (u a) (v a-v₀)
  have hd0 : Filter.Tendsto (fun a=>input D (u a) (v a)-input D (u a) v₀) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hd
  have hs := ((input_continuous D v₀ K hb).tendsto u₀).comp hu
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hd0.add hs
end SHE.OriginalScalarInputContinuity
