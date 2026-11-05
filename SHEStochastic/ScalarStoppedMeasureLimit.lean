module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedMeasureLimit
open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Density agreement on the unhit region gives the same restricted
measure there. -/
theorem restrict_tilt_eq (μ : Measure Ω) (R R' : Ω→ℝ≥0∞) (s : Set Ω) (hs : MeasurableSet s)
    (he : ∀ᵐ x ∂μ,x∈s → R x=R' x) :
    (μ.withDensity R).restrict s=(μ.withDensity R').restrict s := by
  ext A hA
  rw [Measure.restrict_apply hA,Measure.restrict_apply hA,withDensity_apply _ (hA.inter hs),
    withDensity_apply _ (hA.inter hs)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem (hA.inter hs)] with x hx hm
  exact hx hm.2

/-- Probabilities of compatible stopped events converge to their
full-law probabilities. The observation itself may depend on the
localization level, provided its event agrees on the unhit region. -/
theorem event_tendsto (Q : Measure Ω) [IsProbabilityMeasure Q] (Qn : ℕ→Measure Ω)
    [∀ n,IsProbabilityMeasure (Qn n)] (good : ℕ→Set Ω)
    (hg : ∀ n,MeasurableSet (good n)) (hmon : Monotone good)
    (hExhaust : (⋃ n,good n)=univ)
    (hSame : ∀ n,(Qn n).restrict (good n)=Q.restrict (good n))
    (s : Set Ω) (sn : ℕ→Set Ω) (hsn : ∀ n,MeasurableSet (sn n))
    (hEq : ∀ n,∀ᵐ x ∂Q,x∈good n → (x∈s ↔ x∈sn n)) :
    Tendsto (fun n => (Qn n).real (sn n)) atTop (𝓝 (Q.real s)) := by
  have hBad : Tendsto (fun n => Q.real (good n)ᶜ) atTop (𝓝 0) := by
    have hb : (⋂ n,(good n)ᶜ)=(∅ : Set Ω) := by
      rw [←compl_iUnion,hExhaust,compl_univ]
    have hμ := tendsto_measure_iInter_atTop (μ := Q)
      (fun n => (hg n).compl.nullMeasurableSet) (fun n m hnm => compl_subset_compl.mpr (hmon hnm))
      ⟨0,measure_ne_top Q _⟩
    rw [hb,measure_empty] at hμ
    simpa only [Measure.real,ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).tendsto.comp hμ
  have hAgree (n : ℕ) : Q (s∩good n)=(Qn n) (sn n∩good n) := by
    calc
      _ = Q (sn n∩good n) := by
        apply measure_congr
        filter_upwards [hEq n] with x hx
        apply propext
        constructor
        · exact fun ha => ⟨(hx ha.2).mp ha.1,ha.2⟩
        · exact fun ha => ⟨(hx ha.2).mpr ha.1,ha.2⟩
      _ = _ := by
        have he := congrArg (fun m : Measure Ω => m (sn n)) (hSame n)
        simpa only [Measure.restrict_apply (hsn n)] using he.symm
  have hComp (n : ℕ) : (Qn n) (good n)ᶜ=Q (good n)ᶜ := by
    have he := congrArg (fun m : Measure Ω => m univ) (hSame n)
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter] at he
    have hQ := measure_add_measure_compl (μ := Q) (hg n)
    have hQn := measure_add_measure_compl (μ := Qn n) (hg n)
    rw [he,measure_univ] at hQn
    rw [measure_univ] at hQ
    have h := congrArg ENNReal.toReal (hQn.trans hQ.symm)
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h
    have hh := add_left_cancel h
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using congrArg ENNReal.ofReal hh
  have hReal (n : ℕ) :
      |(Qn n).real (sn n)-Q.real s|≤Q.real (good n)ᶜ := by
    have h₁ : Q s≤(Qn n) (sn n)+Q (good n)ᶜ := by
      rw [←measure_inter_add_sdiff (μ := Q) s (hg n),hAgree n]
      exact add_le_add (measure_mono inter_subset_left) (measure_mono (sdiff_subset_compl _ _))
    have h₂ : (Qn n) (sn n)≤Q s+Q (good n)ᶜ := by
      rw [←measure_inter_add_sdiff (μ := Qn n) (sn n) (hg n),←hAgree n,←hComp n]
      exact add_le_add (measure_mono inter_subset_left) (measure_mono (sdiff_subset_compl _ _))
    have h₁' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) h₁
    have h₂' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) h₂
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h₁' h₂'
    simp only [Measure.real]
    exact abs_le.mpr ⟨by linarith [h₁'],by linarith [h₂']⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hBad
  simpa only [Real.norm_eq_abs] using hReal n

end SHEStochastic.ScalarStoppedMeasureLimit
