module

public import SHEStochastic.MatrixFourierMildRealization
public import SHEStochastic.NativeHorizonIntegral
public import SHEStochastic.NativeInputPairing

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixFourierHorizonRestriction
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {H K : ℝ≥0} (hKH : K ≤ H) (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0<β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)

/-- Original Fourier inputs agree under literal extension by zero
whenever their stopping time lies in the smaller horizon. -/
theorem input (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t ≤ K) :
    NativeHorizonIntegral.input hKH
      (StoppedItoInputs.stop F μ K t (MatrixFourierInput.input F μ K G hG hβ hβ1 U hU i a n))=
      StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n) := by
  let r := StoppedItoInputs.stop F μ K t (MatrixFourierInput.input F μ K G hG hβ hβ1 U hU i a n)
  let f : ℝ≥0×Ω → Input (d := d) := (StoppedItoInputs.before (Ω := Ω) t).indicator (fun p => MatrixFourierInput.row K G hG hβ hβ1 U i a n p)
  have hf : @Measurable _ _ F.predictable _ f := by
    letI : MeasurableSpace (ℝ≥0×Ω) := F.predictable
    exact (MatrixFourierInput.predictable F K G hG hβ hβ1 U hU i a n).measurable.indicator (StoppedItoInputs.before_measurable F t)
  have hr : r =ᵐ[energyMeasure μ K] f := by
    filter_upwards [StoppedItoInputs.stop_ae F μ K t (MatrixFourierInput.input F μ K G hG hβ hβ1 U hU i a n),
      MatrixFourierInput.input_ae F μ K G hG hβ hβ1 U hU i a n] with p hs hp
    rw [hs]
    by_cases ht : p∈StoppedItoInputs.before (Ω := Ω) t
    · simpa only [f,Set.indicator_of_mem ht] using hp
    · simp only [f,Set.indicator_of_notMem ht]
  have hrm : @Measurable _ _ (DeterministicItoShift.filtration F 0).predictable _ r := by
    rw [NativeHorizonIntegral.filtration_zero]
    exact (Lp.stronglyMeasurable r).measurable
  have hfm : @Measurable _ _ (DeterministicItoShift.filtration F 0).predictable _ f := by
    rw [NativeHorizonIntegral.filtration_zero]
    exact hf
  have he := DeterministicItoShift.extend_ae F μ H 0 K (by simpa using hKH) hrm hfm hr
  apply NativeInputPairing.process_ext
  filter_upwards [NativeHorizonIntegral.input_ae hKH r,he,
    StoppedItoInputs.stop_ae F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n),
    MatrixFourierInput.input_ae F μ H G hG hβ hβ1 U hU i a n,
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure H) (ν := μ)).ae (timeMeasure_ae_mem H)]
    with p hi he hs hp htime
  rw [hi,he,hs]
  have hbig : (StoppedItoInputs.before (Ω := Ω) t).indicator
      (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n) p=f p := by
    by_cases hbefore : p∈StoppedItoInputs.before (Ω := Ω) t
    · simp only [f,Set.indicator_of_mem hbefore]
      rw [hp]
      have hpt : p.1 ≤ t := by exact_mod_cast (show (p.1 : ℝ)<(t : ℝ) from hbefore).le
      have hpk : (p.1 : ℝ) ≤ K := by exact_mod_cast hpt.trans ht
      have hph : (p.1 : ℝ) ≤ H := by exact_mod_cast (hpt.trans ht).trans hKH
      simp only [MatrixFourierInput.row,FourierHeatInput.multiplier,min_eq_left hpk,min_eq_left hph]
    · simp only [f,Set.indicator_of_notMem hbefore]
  rw [hbig]
  by_cases hq : p.1 ≤ K
  · simp only [DeterministicItoShift.extend,DeterministicItoShift.relative,zero_add,tsub_zero,
      if_pos htime.1,if_pos hq]
  · have hnt : p∉StoppedItoInputs.before (Ω := Ω) t := by
      change ¬(p.1 : ℝ)<(t : ℝ)
      exact not_lt_of_ge (by exact_mod_cast ht.trans (le_of_not_ge hq))
    simp only [DeterministicItoShift.extend,zero_add,if_pos htime.1,if_neg hq,f,Set.indicator_of_notMem hnt]

include hKH in
/-- A native Fourier equation restricts to every smaller horizon while
retaining the original Brownian coordinates and the same state. -/
theorem equation (P : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
    (Q : FiniteScalarIto.Family F μ K (d×FiniteHaar.HaarNode))
    (hW : ∀ i t,t ≤ K → Q.W i t =ᵐ[μ] P.W i t) (Z : Ω → Physical (d := d))
    (he : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU P Z) :
    MatrixFourierMildRealization.RandomEquation F μ K G hG hβ hβ1 U hU Q Z := by
  intro i a n t ht
  have hh := NativeHorizonIntegral.integral hKH P Q MatrixPredictableHaarRotation.basis hW
    (StoppedItoInputs.stop F μ K t (MatrixFourierInput.input F μ K G hG hβ hβ1 U hU i a n))
  rw [input F μ hKH G hG hβ hβ1 U hU i a n t ht] at hh
  have hs := he i a n t (ht.trans hKH)
  rw [←hh] at hs
  exact hs

end SHEStochastic.MatrixFourierHorizonRestriction
