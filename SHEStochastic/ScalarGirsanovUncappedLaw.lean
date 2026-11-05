module

public import SHEStochastic.ScalarGirsanovCoordinateShift
public import SHEStochastic.ScalarStoppedBrownianLimit
public import SHEStochastic.ScalarNativeStoppedTilt
public import SHEStochastic.NativeInputEquiv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovUncappedLaw
open MeasureTheory SHE SHE.PredictableL2 ProbabilityTheory Filter Set
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "Proc" => NativeInputEquiv.inverse F μ H
local notation "S" => ScalarGirsanovCoordinateShift.shift P e
local notation "Q" => NativeGirsanovTilt.measure P e

omit [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] in
theorem probability_of_mass_one (u : Lp C 2 νin)
    (hMass : (∫⁻ ω,ENNReal.ofReal (NativeExponential.density P e (-1) u ω) ∂μ)=1) :
    IsProbabilityMeasure (Q u) := by
  constructor
  rw [NativeGirsanovTilt.measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hMass]

private theorem finite_cap (u : Lp C 2 νin) (K : ℝ) (hK : 0≤K)
    (hCap : ∀ᵐ ω ∂μ,NativeEnergy.energy u ω≤K) (n : ℕ) (a : Fin n → ι) :
    FiniteBrownianLawOn F (Q u) H (fun i => S (Proc u) (a i))
      (fun i j => if a i=a j then 1 else 0) := by
  have ht : FiniteCylindricalIto.processTransport (Proc u)=u :=
    NativeInputEquiv.transport_inverse F μ H u
  have he := NativeBoundedNovikov.energy_transport_ae (Proc u)
  rw [ht] at he
  have hCap' : ∀ᵐ ω ∂μ,StochasticExponential.bracket F μ H (Proc u) ω≤K := by
    filter_upwards [hCap,he] with ω hc he
    exact he ▸ hc
  have h := ScalarGirsanovCoordinateShift.finite_cap P e (Proc u) K hK hCap' n a
  change FiniteBrownianLawOn F
    (ExponentialChangeMeasure.measure μ
      (fun ω => (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (Proc u) ω)
      (StochasticExponential.bracket F μ H (Proc u))) H _ _ at h
  rwa [←NativeGirsanovRows.measure_transport P e (Proc u),ht] at h

/-- Once the mass-one identity is established, the actual uncapped
shift is Brownian against the full filtration under the changed law. -/
theorem finite_law (u : Lp C 2 νin) (U : ℕ → Lp C 2 νin)
    (hMass : (∫⁻ ω,ENNReal.ofReal (NativeExponential.density P e (-1) u ω) ∂μ)=1)
    (hCap : ∀ k,∀ᵐ ω ∂μ,NativeEnergy.energy (U k) ω≤(k : ℝ))
    (hGood : ∀ k : ℕ,∀ᵐ ω ∂μ,NativeEnergy.energy u ω<(k : ℝ) →
      ∀ᵐ t ∂νt,U k (t,ω)=u (t,ω))
    (n : ℕ) (a : Fin n → ι) :
    FiniteBrownianLawOn F (Q u) H (fun i => S (Proc u) (a i))
      (fun i j => if a i=a j then 1 else 0) := by
  let _ : IsProbabilityMeasure (Q u) := probability_of_mass_one P e u hMass
  let _ : ∀ k,IsProbabilityMeasure (Q (U k)) :=
    fun k => NativeGirsanovTilt.probability P e (U k) (k : ℝ) (Nat.cast_nonneg _) (hCap k)
  let good (k : ℕ) : Set Ω := {ω | NativeEnergy.energy u ω<(k : ℝ)}
  have hgood (k : ℕ) : MeasurableSet (good k) :=
    measurableSet_lt (NativeEnergy.stronglyMeasurable u).measurable measurable_const
  have hmon : Monotone good := by
    intro k l hkl ω hω
    change NativeEnergy.energy u ω < (k : ℝ) at hω
    change NativeEnergy.energy u ω < (l : ℝ)
    exact hω.trans_le (Nat.cast_le.mpr hkl)
  have hExhaust : (⋃ k,good k)=univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨k,hk⟩ := exists_nat_gt (NativeEnergy.energy u ω)
    exact mem_iUnion.mpr ⟨k,hk⟩
  have hSame (k : ℕ) : (Q (U k)).restrict (good k)=(Q u).restrict (good k) := by
    apply ScalarStoppedMeasureLimit.restrict_tilt_eq μ _ _ _ (hgood k)
    filter_upwards [hGood k,ScalarNativeIntegralLocality.congr_on_time_fibres P e (U k) u] with ω hg hi hω
    have hF := hg hω
    have he : NativeEnergy.energy (U k) ω=NativeEnergy.energy u ω :=
      integral_congr_ae (hF.mono fun _ ht => congrArg (fun z : C => ‖z‖^2) ht)
    change ENNReal.ofReal (NativeExponential.density P e (-1) (U k) ω)=
      ENNReal.ofReal (NativeExponential.density P e (-1) u ω)
    rw [NativeExponential.density,NativeExponential.density,hi hF,he]
  have hAbs : Q u ≪ μ := withDensity_absolutelyContinuous μ _
  have hm (v : Lp C 2 νin) (i : ι) (t : ℝ≥0) : Measurable (S (Proc v) i t) :=
    (ScalarGirsanovCoordinateShift.adapted P e (Proc v) i t).mono (F.le t) le_rfl
  have hEq (k : ℕ) (i : Fin n) (t : ℝ≥0) :
      ∀ᵐ ω ∂Q u,ω∈good k → S (Proc u) (a i) (min t H) ω=S (Proc (U k)) (a i) (min t H) ω := by
    apply Filter.Eventually.filter_mono hAbs.ae_le
    filter_upwards [hGood k,ScalarGirsanovCoordinateShift.primitive P e (Proc u) (a i),
      ScalarGirsanovCoordinateShift.primitive P e (Proc (U k)) (a i)] with ω hg hu hv hω
    rw [hu _ (min_le_right _ _),hv _ (min_le_right _ _),
      NativeInputEquiv.transport_inverse,NativeInputEquiv.transport_inverse]
    congr 1
    apply integral_congr_ae
    filter_upwards [hg hω] with s hs
    by_cases h : s < min t H <;> simp only [Set.indicator_apply,Set.mem_Iio,h,ite_true,ite_false]
    exact congrArg (inner ℝ (e (a i))) hs.symm
  have hLaw (k : ℕ) :
      FiniteBrownianLawOn F (Q (U k)) H (fun i t => S (Proc (U k)) (a i) (min t H))
        (fun i j => if a i=a j then 1 else 0) := by
    have h := finite_cap P e (U k) (k : ℝ) (Nat.cast_nonneg _) (hCap k) n a
    constructor
    · intro t ht
      convert h.1 t ht using 1
      funext ω
      apply congrArg (WithLp.toLp 2)
      funext i
      change S (Proc (U k)) (a i) (min (t i) H) ω = S (Proc (U k)) (a i) (t i) ω
      rw [min_eq_left (ht i)]
    · intro s t hst ht
      simpa only [min_eq_left ht,min_eq_left (hst.trans ht)] using h.2 s t hst ht
  have h := ScalarStoppedBrownianLimit.finite_law (Q u) (fun k => Q (U k)) good
    hgood hmon hExhaust hSame F H (fun i j => if a i=a j then 1 else 0)
    (fun i t => S (Proc u) (a i) (min t H))
    (fun k i t => S (Proc (U k)) (a i) (min t H))
    (fun i t => hm u (a i) (min t H)) (fun k i t => hm (U k) (a i) (min t H)) hEq hLaw
  constructor
  · intro t ht
    convert h.1 t ht using 1
    funext ω
    apply congrArg (WithLp.toLp 2)
    funext i
    change S (Proc u) (a i) (t i) ω = S (Proc u) (a i) (min (t i) H) ω
    rw [min_eq_left (ht i)]
  · intro s t hst ht
    simpa only [min_eq_left ht,min_eq_left (hst.trans ht)] using h.2 s t hst ht

end SHEStochastic.ScalarGirsanovUncappedLaw
