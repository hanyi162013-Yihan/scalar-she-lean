module

public import SHE.JointLpRepresentative
public import SHE.NativeItoBracket
public import SHE.NonlinearHaarIntegrand

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual jointly measurable spatial representatives of L² states,
including predictable processes and the native period-2π convention.
The nonlinear coefficient identity is spatial AE for every parameter;
no point evaluation on L² is silently assumed. -/
noncomputable section
namespace SHE.PredictableScalarField
open MeasureTheory Set AddCircle CircleHeat FiniteHaar DyadicApproximation
open NativeHeatObservation WordRecursion CoefficientFields
open scoped NNReal ENNReal
local instance predictableScalarField_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance predictableScalarField_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance predictableScalarField_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance predictableScalarField_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance predictableScalarField_realBorel : BorelSpace RealL2 := ⟨rfl⟩

variable {P : Type*}

def unitField (U : P → RealL2) (p : P × AddCircle (1:ℝ)) : ℝ :=
  JointLpRepresentative.representative (haarAddCircle (T := (1:ℝ))) (U p.1,p.2)

def nativeField (U : P → RealL2) (p : P × StoppedFourier.HeatCircle) : ℝ :=
  unitField U (p.1,CircleNormalization.scale (2*Real.pi) 1 p.2)

theorem unitField_measurable [MeasurableSpace P] {U : P → RealL2} (hU : Measurable U) :
    Measurable (unitField U) := by
  have hp : Measurable (fun p : P × AddCircle (1:ℝ) => (U p.1,p.2)) :=
    (hU.comp measurable_fst).prodMk measurable_snd
  have hc := (JointLpRepresentative.representative_measurable (haarAddCircle (T := (1:ℝ)))).comp hp
  exact hc

theorem nativeField_measurable [MeasurableSpace P] {U : P → RealL2} (hU : Measurable U) :
    Measurable (nativeField U) := by
  have hp : Measurable (fun p : P × StoppedFourier.HeatCircle =>
      (p.1,CircleNormalization.scale (2*Real.pi) 1 p.2)) :=
    measurable_fst.prodMk ((CircleNormalization.continuous_scale _ _).measurable.comp measurable_snd)
  exact (unitField_measurable hU).comp hp

theorem unitField_ae (U : P → RealL2) (p : P) :
    (fun x => unitField U (p,x))=ᵐ[haarAddCircle (T := (1:ℝ))] U p :=
  JointLpRepresentative.representative_ae (haarAddCircle (T := (1:ℝ))) (U p)

theorem nativeField_ae_unit (U : P → RealL2) (p : P) :
    (fun x => nativeField U (p,x))=ᵐ[haarAddCircle (T := 2*Real.pi)]
      (fun x => U p (CircleNormalization.scale (2*Real.pi) 1 x)) := by
  have he := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae (unitField_ae U p)
  exact he

/-- Every section is a genuine representative of the rescaled physical
L² state. The exceptional spatial set may depend on the parameter. -/
theorem nativeField_ae_state (U : P → RealL2) (p : P) :
    (fun x => nativeField U (p,x))=ᵐ[haarAddCircle (T := 2*Real.pi)]
      (fun x => (embed (U p) x).re) := by
  have hr := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (realEmbed_ae (U p))
  filter_upwards [nativeField_ae_unit U p,CircleNormalization.push_ae (realEmbed (U p)),hr] with x hx hp hrx
  rw [hx,embed_apply,hp,hrx]
  rfl

theorem nativeField_coefficient_ae (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ z,|a z| ≤ M) (U : P → RealL2) (p : P) :
    (fun x => (CircleNormalization.push (coefficient a ha M hM (U p)) x).re)=ᵐ[haarAddCircle (T := 2*Real.pi)]
      (fun x => a (nativeField U (p,x))) := by
  have hc := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (coefficient_ae a ha M hM (U p))
  filter_upwards [nativeField_ae_unit U p,CircleNormalization.push_ae (coefficient a ha M hM (U p)),hc]
    with x hx hp hc
  rw [hp,hc,hx]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual real-time native scalar field used in physical words. -/
def wordField (U : ℝ≥0 × Ω → RealL2) (ω : Ω) (p : ℝ × StoppedFourier.HeatCircle) : ℝ :=
  nativeField U ((p.1.toNNReal,ω),p.2)

theorem nativeField_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {U : ℝ≥0 × Ω → RealL2} (hU : StronglyMeasurable[𝓕.predictable] U) :
    @Measurable ((ℝ≥0 × Ω) × StoppedFourier.HeatCircle) ℝ
      (𝓕.predictable.prod inferInstance) _ (nativeField U) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact nativeField_measurable hU.measurable

theorem wordField_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {U : ℝ≥0 × Ω → RealL2} (hU : StronglyMeasurable[𝓕.predictable] U) :
    Measurable (fun p : Ω × (ℝ × StoppedFourier.HeatCircle) => wordField U p.1 p.2) := by
  have hUa : Measurable U := (hU.mono (PredictableL2.predictable_le_product 𝓕)).measurable
  have hp : Measurable (fun p : Ω × (ℝ × StoppedFourier.HeatCircle) => ((p.2.1.toNNReal,p.1),p.2.2)) :=
    ((measurable_real_toNNReal.comp measurable_snd.fst).prodMk measurable_fst).prodMk measurable_snd.snd
  exact (nativeField_measurable hUa).comp hp

theorem wordField_section_measurable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {U : ℝ≥0 × Ω → RealL2} (hU : StronglyMeasurable[𝓕.predictable] U) (ω : Ω) :
    Measurable (wordField U ω) := by
  have hp : Measurable (fun p : ℝ × StoppedFourier.HeatCircle => (ω,p)) := measurable_const.prodMk measurable_id
  have he := (wordField_measurable 𝓕 hU).comp hp
  exact he

def coefficientFunction (a : ℝ → ℝ) (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (U : ℝ≥0 × Ω → RealL2) : ℝ≥0 × Ω → EllipticField ell M :=
  fun p => NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (U p)

/-- The literal physical covariance density of the constructed coefficient
is the nonlinear scalar-field covariance density. This equality holds for
every ω and every time, after the genuine spatial AE identification. -/
theorem density_eq (a : ℝ → ℝ) (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (U : ℝ≥0 × Ω → RealL2)
    {n : ℕ} (Z : Fin n → Observation) (ω : Ω) (t : ℝ) :
    CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient (coefficientFunction a ha hell hb U) ω) Z t=
      CovarianceMatrix.densityMatrix (fun p => a (wordField U ω p)) Z t := by
  ext i j
  apply integral_congr_ae
  have hc := nativeField_coefficient_ae a ha M (NonlinearHaarIntegrand.absBound hell hb) U (t.toNNReal,ω)
  filter_upwards [hc] with x hx
  change (CircleNormalization.push (coefficient a ha M (NonlinearHaarIntegrand.absBound hell hb)
      (U (t.toNNReal,ω))) x).re * heatRow Z t x i * heatRow Z t x j=
    a (nativeField U ((t.toNNReal,ω),x))*heatRow Z t x i*heatRow Z t x j
  rw [hx]

end SHE.PredictableScalarField
