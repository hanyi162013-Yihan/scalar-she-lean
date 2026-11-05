module

public import SHEStochastic.ScalarLipschitzDampedMoments
public import SHE.PredictableExponential
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzMomentBall
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar
open ScalarLipschitzDampedEnergy ScalarLipschitzDampedMoments ScalarLipschitzItoMoment ScalarLipschitzRawBounds
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local notation "tm" => PredictableL2.timeMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0}

def Ball (D : ℝ) : Set (Process (E := RealL2) F μ H) :=
  {u | ∀ᵐ t ∂tm H,moment 16 (fun ω => u (t,ω)) μ≤ENNReal.ofReal D}

theorem zero_mem (D : ℝ) : (0 : Process (E := RealL2) F μ H)∈Ball D := by
  change ∀ᵐ t ∂tm H,moment 16 (fun ω => (0 : Process (E := RealL2) F μ H) (t,ω)) μ≤_
  have h := Measure.ae_ae_of_ae_prod (ae_eq_of_ae_eq_trim
    (Lp.coeFn_zero (α := ℝ≥0×Ω) (E := RealL2) (p := 2)
      (μ := (energyMeasure μ H).trim (predictable_le_product F))))
  filter_upwards [h] with t ht
  rw [moment_congr ht]
  simp [moment]

/-- The essential timewise moment ball is closed in the predictable
L² norm. Extract a product-space subsequence, then use Fatou on each
time fibre. -/
theorem isClosed_ball (D : ℝ) : IsClosed (Ball (F := F) (μ := μ) (H := H) D) := by
  apply isClosed_of_closure_subset
  intro u hu
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp hu
  let j := ambientIsometry (E := RealL2) (energyMeasure μ H) (predictable_le_product F)
  have hJ : Tendsto (fun n => j (v n)) atTop (𝓝 (j u)) :=
    j.continuous.continuousAt.tendsto.comp hlim
  obtain ⟨φ,_,hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hJ).exists_seq_tendsto_ae
  have hφ' : ∀ᵐ p ∂energyMeasure μ H,Tendsto (fun n => v (φ n) p) atTop (𝓝 (u p)) := by
    filter_upwards [hφ,ambient_ae (energyMeasure μ H) (predictable_le_product F) u,
      ae_all_iff.mpr (fun n => ambient_ae (energyMeasure μ H) (predictable_le_product F) (v (φ n)))]
      with p hp hu hv
    change Tendsto (fun n => j (v (φ n)) p) atTop (𝓝 (j u p)) at hp
    rw [show j u p=u p from hu,show (fun n => j (v (φ n)) p)=(fun n => v (φ n) p) from funext hv] at hp
    exact hp
  have hVm (n : ℕ) : Measurable (v (φ n) : ℝ≥0×Ω → RealL2) :=
    ((Lp.stronglyMeasurable (v (φ n))).mono (predictable_le_product F)).measurable
  have hh : ∀ᵐ t ∂tm H,∀ n,moment 16 (fun ω => v (φ n) (t,ω)) μ≤ENNReal.ofReal D :=
    ae_all_iff.mpr (fun n => hv (φ n))
  change ∀ᵐ t ∂tm H,moment 16 (fun ω => u (t,ω)) μ≤_
  filter_upwards [Measure.ae_ae_of_ae_prod hφ',hh] with t ht hb
  calc
    _ = ∫⁻ ω,liminf (fun n => ENNReal.ofReal (‖v (φ n) (t,ω)‖^16)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with ω hω
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hω.norm.pow 16)).liminf_eq.symm
    _ ≤ liminf (fun n => moment 16 (fun ω => v (φ n) (t,ω)) μ) atTop :=
      lintegral_liminf_le (fun n =>
        (((hVm n).comp (measurable_const.prodMk measurable_id)).norm.pow_const _).ennreal_ofReal)
    _ ≤ _ := liminf_le_of_frequently_le' (Filter.Eventually.of_forall hb).frequently

omit [IsProbabilityMeasure μ] in
theorem moment_scale {f : Ω → RealL2} (hf : Measurable f) (a : ℝ) :
    moment 16 (fun ω => a • f ω) μ=ENNReal.ofReal (|a|^16)*moment 16 f μ := by
  unfold moment
  simp_rw [norm_smul,Real.norm_eq_abs,mul_pow,ENNReal.ofReal_mul (pow_nonneg (abs_nonneg a) 16)]
  exact lintegral_const_mul'' _ ((hf.norm.pow_const (16 : ℕ)).ennreal_ofReal.aemeasurable)

theorem scaled_fibre (γ : ℝ) (u : Process (E := RealL2) F μ H) :
    ∀ᵐ t ∂tm H, moment 16 (fun ω => (PredictableExponential.scale F μ H (-γ) u) (t,ω)) μ =
      weightedMoment (μ := μ) γ (fun s ω => u (s,ω)) t := by
  have hm : Measurable (u : ℝ≥0×Ω → RealL2) :=
    ((Lp.stronglyMeasurable u).mono (predictable_le_product F)).measurable
  filter_upwards [Measure.ae_ae_of_ae_prod (PredictableExponential.ae F μ H (-γ) u),
    timeMeasure_ae_mem H] with t ht htime
  have hu : Measurable (fun ω => u (t,ω)) := hm.comp (measurable_const.prodMk measurable_id)
  rw [moment_congr ht]
  change moment 16 (fun ω => (Real.exp ((-γ)*min (t : ℝ) (H : ℝ))) • u (t,ω)) μ = _
  rw [moment_scale hu,min_eq_left (by exact_mod_cast htime.2),abs_of_pos (Real.exp_pos _),weightedMoment,timeWeight_pow]
  have hh : Real.exp ((-γ)*(t : ℝ))^16=Real.exp (-16*γ*(t : ℝ)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hh]

/-- A timewise sixteenth moment gives an integrated second moment on
the finite horizon and the predictable process is its own L² class. -/
theorem integrated {U : ℝ≥0 → Ω → RealL2}
    (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    {D : ℝ≥0∞} (hD : D≠⊤)
    (hM : ∀ᵐ t ∂tm H,moment 16 (U t) μ≤D) :
    Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H) := by
  let f := fun p : ℝ≥0×Ω => ENNReal.ofReal (‖U p.1 p.2‖^2)
  have hm := hU.mono (predictable_le_product F)
  have hf : Measurable f := (hm.norm.pow 2).measurable.ennreal_ofReal
  refine integrable_of_density (Function.uncurry U) hm (fun _ => 1) measurable_const f hf
    (1+D) (ENNReal.add_ne_top.mpr ⟨by simp,hD⟩) ?_ ?_ (Filter.Eventually.of_forall fun p => by rw [one_mul]; exact le_rfl)
  · filter_upwards [hM] with t ht
    calc
      _ ≤ ∫⁻ ω,1+ENNReal.ofReal (‖U t ω‖^16) ∂μ := by
        apply lintegral_mono
        intro ω
        change ENNReal.ofReal (‖U t ω‖^2)≤1+ENNReal.ofReal (‖U t ω‖^16)
        rw [←ENNReal.ofReal_one,←ENNReal.ofReal_add zero_le_one (by positivity)]
        exact ENNReal.ofReal_le_ofReal (sq_le_one_add_sixteen (norm_nonneg _))
      _ ≤ _ := by
        rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
        exact add_le_add le_rfl ht
  · rw [lintegral_const,one_mul,timeMeasure_mass]
    exact ENNReal.ofReal_ne_top

def processOf (U : ℝ≥0 → Ω → RealL2)
    (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hE : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    Process (E := RealL2) F μ H := by
  letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
  have hm := (memLp_two_iff_integrable_sq_norm
    ((hU.mono (predictable_le_product F)).aestronglyMeasurable (μ := energyMeasure μ H))).mpr hE
  have hp : MemLp (Function.uncurry U) 2 ((energyMeasure μ H).trim (predictable_le_product F)) :=
    (eLpNorm_trim (predictable_le_product F) hU).trans_lt hm.eLpNorm_lt_top
  exact hp.toLp (Function.uncurry U)

omit [IsProbabilityMeasure μ] in
theorem processOf_ae (U : ℝ≥0 → Ω → RealL2)
    (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hE : Integrable (fun p : ℝ≥0×Ω => ‖U p.1 p.2‖^2) (energyMeasure μ H)) :
    processOf U hU hE =ᵐ[energyMeasure μ H] Function.uncurry U := by
  unfold processOf
  exact ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp _)

end SHEStochastic.ScalarLipschitzMomentBall
