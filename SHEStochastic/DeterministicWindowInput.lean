module

public import SHE.DeterministicItoShiftInput
public import SHE.StoppedInputParameter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.DeterministicWindowInput
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ]
  (T v h : ℝ≥0) (hvh : v+h≤T)

/-- A local predictable input with a known literal shifted row becomes
exactly the difference of the two original global stopped inputs.
Only the single joining time is discarded, as allowed by time measure. -/
theorem stopped (u : Process (E := C) F μ T)
    (w : Process (E := C) (DeterministicItoShift.filtration F v) μ h)
    (U V : ℝ≥0×Ω → C)
    (hV : StronglyMeasurable[(DeterministicItoShift.filtration F v).predictable] V)
    (hu : u =ᵐ[energyMeasure μ T] U) (hw : w =ᵐ[energyMeasure μ h] V)
    (c : ℝ) (hrow : ∀ t,t≤h → ∀ ω,c • V (t,ω)=U (v+t,ω))
    (t : ℝ≥0) (ht : t≤h) :
    c • DeterministicItoShift.input F μ T v h hvh
      (StoppedItoInputs.stop (DeterministicItoShift.filtration F v) μ h t w)=
      StoppedItoInputs.stop F μ T (v+t) u-StoppedItoInputs.stop F μ T v u := by
  let S := StoppedItoInputs.stop (DeterministicItoShift.filtration F v) μ h t w
  let raw := (StoppedItoInputs.before t).indicator V
  have hm : @Measurable _ _ (DeterministicItoShift.filtration F v).predictable _ raw :=
    hV.measurable.indicator (StoppedItoInputs.before_measurable _ t)
  have he : S =ᵐ[energyMeasure μ h] raw := by
    filter_upwards [StoppedItoInputs.stop_ae _ μ h t w,hw] with p hp hwp
    rw [hp]
    change (StoppedItoInputs.before t).indicator w p=(StoppedItoInputs.before t).indicator V p
    by_cases ht : p∈StoppedItoInputs.before t
    · simpa only [indicator_of_mem ht] using hwp
    · simp only [indicator_of_notMem ht]
  have hx := DeterministicItoShift.extend_ae F μ T v h hvh (Lp.stronglyMeasurable S).measurable hm he
  have hn : ∀ᵐ p ∂energyMeasure μ T,p.1≠v :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure T).ae_ne v)
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [DeterministicItoShift.input_ae F μ T v h hvh S,hx,hu,hn,
    StoppedItoInputs.stop_ae F μ T (v+t) u,StoppedItoInputs.stop_ae F μ T v u,
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul c (DeterministicItoShift.input F μ T v h hvh S)),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub (StoppedItoInputs.stop F μ T (v+t) u) (StoppedItoInputs.stop F μ T v u))]
    with p hi hx hu hn h1 h0 hs hd
  rw [hs,hd]
  simp only [Pi.smul_apply,Pi.sub_apply]
  rw [hi,hx,h1,h0]
  change c • DeterministicItoShift.extend v h raw p=
    (StoppedItoInputs.before (v+t)).indicator u p-(StoppedItoInputs.before v).indicator u p
  by_cases hp : v<p.1
  · have hnot : p∉StoppedItoInputs.before v := not_lt.mpr hp.le
    rw [indicator_of_notMem hnot]
    by_cases hph : p.1≤v+h
    · have hlocal : p.1-v≤h := tsub_le_iff_right.mpr (by simpa only [add_comm] using hph)
      have hback : v+(p.1-v)=p.1 := add_tsub_cancel_of_le hp.le
      have hbefore : (p.1-v : ℝ≥0)<t ↔ p.1<v+t := by
        constructor
        · intro hh
          calc
            p.1 = (p.1-v)+v := (tsub_add_cancel_of_le hp.le).symm
            _ < t+v := add_lt_add_left hh v
            _ = v+t := add_comm _ _
        · intro hh
          exact (tsub_lt_iff_left hp.le).mpr hh
      simp only [DeterministicItoShift.extend,if_pos hp,if_pos hph,raw,DeterministicItoShift.relative,
        StoppedItoInputs.before,indicator_apply,mem_setOf_eq]
      by_cases hb : p.1<v+t
      · have hl : p.1-v<t := hbefore.mpr hb
        have hbR : (p.1 : ℝ)<(v : ℝ)+(t : ℝ) := by exact_mod_cast hb
        have hlR : ((p.1-v : ℝ≥0) : ℝ)<(t : ℝ) := by exact_mod_cast hl
        rw [if_pos hlR,if_pos hbR,sub_zero,hrow _ hlocal p.2]
        rw [hback,hu]
      · have hl := mt hbefore.mp hb
        have hbR : ¬(p.1 : ℝ)<(v : ℝ)+(t : ℝ) := by exact_mod_cast hb
        have hlR : ¬((p.1-v : ℝ≥0) : ℝ)<(t : ℝ) := by exact_mod_cast hl
        simp only [if_neg hlR,if_neg hbR,smul_zero,sub_zero]
    · have hb : p∉StoppedItoInputs.before (v+t) := by
        have hh : v+t≤v+h := add_le_add le_rfl ht
        exact not_lt.mpr (hh.trans (le_of_not_ge hph))
      rw [indicator_of_notMem hb]
      simp only [DeterministicItoShift.extend,if_pos hp,if_neg hph,smul_zero,sub_self]
  · have hpv : p.1<v := lt_of_le_of_ne (le_of_not_gt hp) hn
    have h0 : p∈StoppedItoInputs.before v := hpv
    have h1 : p∈StoppedItoInputs.before (v+t) := hpv.trans_le le_self_add
    rw [indicator_of_mem h1,indicator_of_mem h0]
    simp only [DeterministicItoShift.extend,if_neg hp,smul_zero,sub_self]

end SHEStochastic.DeterministicWindowInput
