module

public import SHEStochastic.ScalarNativeIntegralLocality
public import SHEStochastic.ScalarDriftDensityLocalization

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarNativeStoppedTilt
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "I" => FiniteCylindricalIto.rawIntegral P.toCoordinates e

local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H

omit [DecidableEq ι] in
include e in
/-- The stopped control uses the actual predictable accumulated
energy. At paths below the terminal threshold it agrees with the
original control on the entire physical time fibre. -/
theorem exists_stops (u : Lp C 2 νin) :
    ∃ (A : ℝ≥0→Ω→ℝ), StronglyMeasurable[F.predictable] (Function.uncurry A) ∧
      (∀ᵐ ω ∂μ, ∀ t,A t ω=TimeEnergyCap.primitive (H := H) (fun r => ‖u (r,ω)‖^2) t) ∧
      ∃ U : ℕ → Lp C 2 νin,
        (∀ n,U n =ᵐ[νin] {p : ℝ≥0×Ω | A p.1 p.2 < (n : ℝ)}.indicator u) ∧
        (∀ n : ℕ,∀ᵐ ω ∂μ,NativeEnergy.energy (U n) ω≤(n : ℝ)) ∧
        (∀ n : ℕ,∀ᵐ ω ∂μ,NativeEnergy.energy u ω<(n : ℝ) →
          ∀ᵐ t ∂νt,U n (t,ω)=u (t,ω)) := by
  classical
  obtain ⟨A,hA,hAeq⟩ := NativePredictableEnergy.exists_version e u
  let S (n : ℕ) : Set (ℝ≥0×Ω) := {p | A p.1 p.2 < (n : ℝ)}
  have hS (n : ℕ) : MeasurableSet[F.predictable] (S n) :=
    measurableSet_lt hA.measurable measurable_const
  let hm (n : ℕ) := (Lp.memLp u).indicator (hS n).nullMeasurableSet
  let U (n : ℕ) : Lp C 2 νin := (hm n).toLp ((S n).indicator u)
  have hU (n : ℕ) : U n =ᵐ[νin] (S n).indicator u := (hm n).coeFn_toLp
  refine ⟨A,hA,hAeq,U,hU,?_,?_⟩
  · intro n
    have hE := NativeEnergy.energy_ae_of_ae (U n) _ (hU n)
    filter_upwards [hE,hAeq,(NativeEnergy.product_memLp u).norm.integrable_sq.prod_left_ae]
      with ω hEω hAω hiω
    rw [hEω]
    have he : (fun r => ‖(S n).indicator u (r,ω)‖^2) =
        {r | TimeEnergyCap.primitive (H := H) (fun r => ‖u (r,ω)‖^2) r < (n : ℝ)}.indicator
          (fun r => ‖u (r,ω)‖^2) := by
      funext r
      have hAr : A r ω=TimeEnergyCap.primitive (H := H) (fun r => ‖u (r,ω)‖^2) r := hAω r
      simp only [S,Set.indicator,Set.mem_ofPred_eq,←hAr]
      split <;> simp
    rw [he]
    exact (TimeEnergyCap.capped_integral_le hiω (fun _ => sq_nonneg _) (n : ℝ) (Nat.cast_nonneg _)).trans
      (min_le_right _ _)
  · intro n
    have hp := ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) (hU n)
    have hFibre := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := μ) (ν := νt)).quasiMeasurePreserving.ae hp)
    filter_upwards [hFibre,hAeq,(NativeEnergy.product_memLp u).norm.integrable_sq.prod_left_ae]
      with ω hUω hAω hIω hGood
    filter_upwards [hUω,ae_restrict_mem measurableSet_Ioc] with t ht hTime
    have ht' : t≤H+1 := hTime.2.trans (le_add_of_nonneg_right zero_le_one)
    have hMon := TimeEnergyCap.monotone_primitive hIω (fun r => sq_nonneg ‖u (r,ω)‖) ht'
    rw [TimeEnergyCap.primitive_terminal] at hMon
    have hS' : (t,ω)∈S n := by
      change A t ω<(n : ℝ)
      rw [hAω t]
      exact hMon.trans_lt hGood
    exact ht.trans (Set.indicator_of_mem hS' _)

local notation "D" a:max u:max => fun ω => ENNReal.ofReal (NativeExponential.density P e a u ω)

/-- The existing bounded-energy Novikov theorem supplies the stopped
probabilities. The stopped tilted-law energy estimate supplies the
mass-one identity for the actual unstopped cylindrical exponential. -/
theorem mass_one (a : ℝ) (u : Lp C 2 νin) (U : ℕ→Lp C 2 νin)
    (hCap : ∀ n,∀ᵐ ω ∂μ,NativeEnergy.energy (U n) ω≤(n : ℝ))
    (hGood : ∀ n : ℕ,∀ᵐ ω ∂μ,NativeEnergy.energy u ω<(n : ℝ) →
      ∀ᵐ t ∂νt,U n (t,ω)=u (t,ω))
    (K : ℝ≥0) (hEnergy : ∀ n, (∫⁻ ω,ENNReal.ofReal (NativeEnergy.energy u ω)
      ∂(μ.withDensity (D a (U n))))≤K) :
    (∫⁻ ω,(D a u) ω ∂μ)=1 := by
  let A := fun ω => (NativeEnergy.energy u ω).toNNReal
  have hA : Measurable A := (NativeEnergy.stronglyMeasurable u).measurable.real_toNNReal
  have hm (n : ℕ) : Measurable (D a (U n)) :=
    (NativeExponential.stronglyMeasurable P e a (U n)).measurable.ennreal_ofReal
  have hOne (n : ℕ) : (∫⁻ ω,(D a (U n)) ω ∂μ)=1 := by
    obtain ⟨hLp,hOne,_⟩ := NativeBoundedExponential.bounded_energy P e a (U n) (n : ℝ)
      (Nat.cast_nonneg _) (hCap n)
    have hi := hLp.integrable (by norm_num)
    rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω => (Real.exp_pos _).le)),hOne,ENNReal.ofReal_one]
  have hAeq (ω : Ω) : (A ω : ℝ)=NativeEnergy.energy u ω :=
    Real.coe_toNNReal _ (integral_nonneg (fun _ => sq_nonneg _))
  have hAgree (n : ℕ) : ∀ᵐ ω ∂μ,A ω<(n : ℝ≥0) → (D a (U n)) ω=(D a u) ω := by
    filter_upwards [hGood n,ScalarNativeIntegralLocality.congr_on_time_fibres P e (U n) u] with ω hg hi hω
    have hω' : NativeEnergy.energy u ω<(n : ℝ) := by
      rw [←hAeq]
      exact_mod_cast hω
    have hF := hg hω'
    have he : NativeEnergy.energy (U n) ω=NativeEnergy.energy u ω :=
      integral_congr_ae (hF.mono (fun _ ht => congrArg (fun z : C => ‖z‖^2) ht))
    change ENNReal.ofReal (NativeExponential.density P e a (U n) ω)=
      ENNReal.ofReal (NativeExponential.density P e a u ω)
    rw [NativeExponential.density,NativeExponential.density,hi hF,he]
  exact ScalarDriftDensityLocalization.mass_one μ A hA (D a u) (fun n => D a (U n))
    hm hOne hAgree K hEnergy

end SHEStochastic.ScalarNativeStoppedTilt
