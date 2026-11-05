module

public import SHE.PositiveGapObservations
public import SHE.StoppedIntegralVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Concrete observations on a local window ending at b, even when their
original targets lie below the global noise horizon h. Inputs and paths
are stopped at b, so the same universal ordinary Itô formula applies. -/
noncomputable section
namespace SHE.LocalNativeObservations
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality NativeObservationCovariance
open PositiveGapObservations WordRecursion StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
local instance localNativeObservations_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance localNativeObservations_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance localNativeObservations_rowSigma : MeasurableSpace RealHaarInput := borel RealHaarInput
local instance localNativeObservations_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance localNativeObservations_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

def stoppedValue {n : ℕ} (δ : ℝ) (Z : Fin n → Observation) (U : ℝ≥0 × Ω → RealL2)
    (b : ℝ≥0) (p : ℝ≥0 × Ω) : WordRecursion.State n := value δ Z U (min p.1 b,p.2)

theorem stoppedValue_continuous {n : ℕ} (δ : ℝ) (Z : Fin n → Observation)
    (U : ℝ≥0 × Ω → RealL2) (b : ℝ≥0) {ω : Ω} (hc : Continuous (fun t => U (t,ω))) :
    Continuous (fun t => stoppedValue δ Z U b (t,ω)) := by
  have ht : Continuous (fun t : ℝ≥0 => min t b) := continuous_id.min continuous_const
  have he := (value_continuous δ Z U hc).comp ht
  exact he

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)

theorem stop_observation_process {ell M T : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
    (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    (b t : ℝ≥0) (hb : (b:ℝ) < T) (x : HeatCircle) :
    stop 𝓕 μ h t (NativeObservationProcess.process 𝓕 μ h hell hM f hf hb x)=
      NativeObservationProcess.process 𝓕 μ h hell hM f hf
        (show ((min t b:ℝ≥0):ℝ) < T by exact lt_of_le_of_lt (by exact_mod_cast min_le_right t b) hb) x := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have hmin : ((min t b:ℝ≥0):ℝ) < T := lt_of_le_of_lt (by exact_mod_cast min_le_right t b) hb
  filter_upwards [stop_ae 𝓕 μ h t (NativeObservationProcess.process 𝓕 μ h hell hM f hf hb x),
    NativeObservationProcess.process_ae 𝓕 μ h hell hM f hf hb x,
    NativeObservationProcess.process_ae 𝓕 μ h hell hM f hf hmin x] with p hs hb' hm
  rw [hs,hm]
  simp only [Set.indicator_apply,before,Set.mem_setOf_eq]
  rw [hb',NativeObservationProcess.integrand_eq hell f hb,NativeObservationProcess.integrand_eq hell f hmin]
  simp only [NNReal.coe_min,lt_min_iff]
  by_cases ht : (p.1:ℝ) < t <;> by_cases hb : (p.1:ℝ) < b <;> simp [ht,hb]

variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n → Observation) (b : ℝ≥0)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(b:ℝ))

def rows : Fin n → Process (E := RealHaarInput) 𝓕 μ h := fun i =>
  NativeObservationProcess.process 𝓕 μ h hell hM f hf
    (show (b:ℝ) < (Z i).target by have := hgap i; linarith) (Z i).center

theorem integral_representation
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J) (u : RealL2) (U : ℝ≥0 × Ω → RealL2)
    (v : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : ∀ t : ℝ≥0,t ≤ h → v t =ᵐ[energyMeasure μ h]
      (fun p => kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)))
    (hmild : ∀ (t : ℝ≥0),t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=heat t u+I.integral (v t) ω)
    (hb : b ≤ h) (t : ℝ≥0) :
    (fun ω => stoppedValue δ Z U b (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ h J (initial Z u) (rows 𝓕 μ h hell hM f hf Z b hδ hgap) t := by
  have hrt : min t b ≤ h := (min_le_right t b).trans hb
  have htarget (i : Fin n) : ((min t b:ℝ≥0):ℝ) < (Z i).target := by
    have hmin : ((min t b:ℝ≥0):ℝ) ≤ b := by exact_mod_cast min_le_right t b
    have := hgap i
    linarith
  have he (i : Fin n) := observe_mild_solution I J hIJ hell hM f hf (htarget i) (min t b).2
    (Z i).center u (v (min t b)) (hv _ hrt) (fun ω => U (min t b,ω)) (hmild _ hrt)
  filter_upwards [ae_all_iff.mpr he] with ω hω
  ext i
  change coordinate δ (Z i).target (Z i).center U (min t b,ω)=
    functional (Z i).target (Z i).center u+
      J.integral (stop 𝓕 μ h t (rows 𝓕 μ h hell hM f hf Z b hδ hgap i)) ω
  have hg : δ ≤ (Z i).target-((min t b:ℝ≥0):ℝ) :=
    (hgap i).trans (sub_le_sub_left (by exact_mod_cast min_le_right t b) _)
  rw [coordinate_eq_functional hδ U _ _ hg,functional_physical (sub_pos.mpr (htarget i))]
  rw [rows,stop_observation_process 𝓕 μ h hell hM f hf b t _ (Z i).center]
  exact hω i

theorem predictable_of_representation (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (z : WordRecursion.State n) (U : ℝ≥0 × Ω → RealL2)
    (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (hRep : ∀ t : ℝ≥0,(fun ω => stoppedValue δ Z U b (t,ω))=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ h J z (rows 𝓕 μ h hell hM f hf Z b hδ hgap) t) :
    StronglyMeasurable[𝓕.predictable] (stoppedValue δ Z U b) := by
  apply NullCompleteFiltration.predictable_of_continuous_versions 𝓕 μ hnull
    (fun t ω => stoppedValue δ Z U b (t,ω))
  · intro t
    obtain ⟨V,hV,he⟩ := StoppedIntegralVersions.vectorIntegral_adapted_version 𝓕 μ h J z
      (rows 𝓕 μ h hell hM f hf Z b hδ hgap) t
    exact ⟨V,hV,(hRep t).trans he⟩
  · intro ω
    exact stoppedValue_continuous δ Z U b (hc ω)

end SHE.LocalNativeObservations
