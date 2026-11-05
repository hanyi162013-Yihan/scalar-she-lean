module

public import SHEStochastic.MatrixPointJointMoments
public import SHEStochastic.HeatParameterContinuity
public import SHEStochastic.HeatParameterInitialBound
public import SHEStochastic.KolmogorovFieldTightness
public import SHEStochastic.FiniteMarginalTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixPointFieldTightness
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.FiniteHaar MatrixInfiniteHaar
open HeatParameterCover HeatParameterCoordinates MatrixPointJointMoments
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (U : ℝ) (hU : 0 ≤ U) (Q : ℝ≥0 × Ω → Profile d)
  (hUpper : ∀ p, (Q p).upper ≤ U) (hH : (H : ℝ) ≤ 1)
  (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
    (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))
  (N : FiniteScalarIto.Family F μ H (d × HaarNode))

/-- Continuous native matrix Haar point fields, with the actual zero
initial trace. All dyadic moments come from scalar heat geometry and BDG. -/
theorem exists_version (i : d) :
    ∃ Y : Ω → C(Parameter,ℝ), Measurable Y ∧
      (∀ p, (fun ω => Y ω p) =ᵐ[μ] value F μ H U hU Q hUpper hH hQ N p i) ∧
      ∀ᵐ ω ∂μ, ∀ p, Y ω (zeroTime p) = 0 := by
  obtain ⟨Y,hm,he,hc⟩ := HeatParameterContinuity.exists_of_dyadic_moments μ
    (fun p ω => value F μ H U hU Q hUpper hH hQ N p i ω)
    (fun p => (Lp.stronglyMeasurable (value F μ H U hU Q hUpper hH hQ N p i)).measurable)
    (1/8) (by norm_num) (momentConstant U H) (fun k => (momentConstant_finite U H k).ne)
    (fun k p q => native_moment F μ H U hU Q hUpper hH hQ N p q i k)
  let Z (ω : Ω) : C(Parameter,ℝ) := ⟨fun p => Y p ω,hc ω⟩
  have hz (p : Parameter) : Y (zeroTime p) =ᵐ[μ] fun _ => (0 : ℝ) := by
    have h := value_zero F μ H U hU Q hUpper hH hQ N (zeroTime p) i (GlobalHeatParameter.zeroTime_time H p)
    apply (he (zeroTime p)).trans
    rw [h]
    simpa using (Lp.coeFn_zero ℝ 2 μ)
  exact ⟨Z,ContinuousMap.measurable_iff_eval.mpr hm,he,
    HeatParameterInitialBound.simultaneous_zero μ Y hc hz⟩

/-- Uniformly bounded coupled matrix covariance fields have jointly
tight native point-field laws. The profiles and Brownian realizations
may vary; the original dependence of all components is retained. -/
theorem exists_tight_versions
    (Qs : ℕ → ℝ≥0 × Ω → Profile d) (hUpperS : ∀ m p, (Qs m p).upper ≤ U)
    (hQs : ∀ m, @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Qs m z.1).value z.2))
    (Ns : ℕ → FiniteScalarIto.Family F μ H (d × HaarNode)) :
    ∃ Y : ℕ → Ω → (d → C(Parameter,ℝ)),
      (∀ m, Measurable (Y m)) ∧
      (∀ (i : d) (m : ℕ) (p : Parameter), (fun ω => Y m ω i p) =ᵐ[μ]
        value F μ H U hU (Qs m) (hUpperS m) hH (hQs m) (Ns m) p i) ∧
      (∀ m, ∀ᵐ ω ∂μ, ∀ i p, Y m ω i (zeroTime p) = 0) ∧
      IsTightMeasureSet (Set.range (fun m => μ.map (Y m))) := by
  choose Z hm he hz using fun (i : d) (m : ℕ) =>
    exists_version F μ H U hU (Qs m) (hUpperS m) hH (hQs m) (Ns m) i
  have ht (i : d) : IsTightMeasureSet (Set.range (fun m => μ.map (Z i m))) := by
    let p₀ : Parameter := ⟨0,by simp [HeatParameterCover.region]⟩
    let M : ℝ≥0 := (momentConstant U H 5).toNNReal
    have hM : (M : ℝ≥0∞) = momentConstant U H 5 :=
      ENNReal.coe_toNNReal (momentConstant_finite U H 5).ne
    apply KolmogorovFieldTightness.tight (fun _ : ℕ => μ) (Z i) (hm i) (zeroTime p₀)
      (fun m => (hz i m).mono fun ω h => h p₀) parameter_cover
      (by norm_num) (by norm_num : (0 : ℝ) < 2) (p := 64) (q := 4) (M := M) (α := 1/64)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    intro m
    apply BDGKolmogorov.of_nat_moments μ (fun p ω => Z i m ω p)
      (fun p => (ContinuousMap.measurable_eval p).comp (hm i m))
      64 (by norm_num) 4 (by norm_num) M
    intro p q
    calc
      _ = ∫⁻ ω, ENNReal.ofReal
          (‖value F μ H U hU (Qs m) (hUpperS m) hH (hQs m) (Ns m) p i ω-
            value F μ H U hU (Qs m) (hUpperS m) hH (hQs m) (Ns m) q i ω‖^64) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [he i m p,he i m q] with ω hp hq
        rw [hp,hq]
      _ ≤ momentConstant U H 5*edist p q^(4 : ℝ) := by
        convert native_moment F μ H U hU (Qs m) (hUpperS m) hH (hQs m) (Ns m) p q i 5 using 1 <;> norm_num [value]
      _ = _ := by rw [hM]
  let Y : ℕ → Ω → (d → C(Parameter,ℝ)) := fun m ω i => Z i m ω
  have hY (m : ℕ) : Measurable (Y m) := measurable_pi_iff.mpr (fun i => hm i m)
  refine ⟨Y,hY,he,?_,FiniteMarginalTightness.tight μ Y hY ht⟩
  intro m
  exact ae_all_iff.mpr (fun i => hz i m)

end SHEStochastic.MatrixPointFieldTightness
