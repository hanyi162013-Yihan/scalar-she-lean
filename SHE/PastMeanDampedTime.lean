module

public import SHE.PastMeanTimeIntegral
public import SHE.MeanDampedTime

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalScoreChain QuarterSpatialEvent HistoryProductMeasure PhysicalParentGeometry
variable {R : ReferenceData} (L : Level R StoppedFourier.HeatCircle 1)

theorem totalIntegrand_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (C : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) : Measurable (totalIntegrand L P ell C k q fresh A0 ν) := by
  have he : totalIntegrand L P ell C k q fresh A0 ν=
      fun p=>∑ i : Fin (GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).length,
        activeFactor L P ell C k q fresh A0 ν
          ((GaussianAssignmentBlocks.assignments (m:=k+1) (List.finRange k)).get i) p := by
    funext p
    exact totalIntegrand_eq_sum L P ell C k q fresh A0 ν p
  rw [he]
  exact Finset.measurable_sum Finset.univ (fun i _=>activeFactor_measurable L P ell C k q fresh A0 ν _)

theorem totalIntegrand_nonneg (P : CanonicalCovariance.ProfileParameters) {ell : ℝ} (hell : 0<ell)
    (C : ℕ→ℝ) (hC : ∀ j,0≤C j) (k : ℕ) (q fresh A0 ν : ℝ)
    (p : History StoppedFourier.HeatCircle k) : 0≤totalIntegrand L P ell C k q fresh A0 ν p := by
  rw [totalIntegrand_eq_sum]
  exact Finset.sum_nonneg (fun i _=>activeFactor_nonneg L P hell C hC k q fresh A0 ν _ p)

/-- Retained quarter-row damping acts on the actual relative-age word
density, before the old times are integrated. -/
theorem damped_integrand_bound (P : CanonicalCovariance.ProfileParameters)
    {ell : ℝ} (hell : 0<ell) (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j)
    (k : ℕ) (q A0 ν Λ ε : ℝ) (hΛ : 0<Λ) (hε : 0≤ε) (hε1 : ε≤1)
    (p : History StoppedFourier.HeatCircle k) :
    exp (-Λ*((carrier L k).terminal p-q)/4)*
      totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν p≤
      ((4:ℝ)^ε*Λ^(-ε))*totalIntegrand L P ell Cs k q (1/2-ε) A0 ν p := by
  unfold totalIntegrand
  split_ifs with ha
  · have hd : 0<(carrier L k).terminal p-q := sub_pos.mpr ha.2
    have hB : 0≤timeWeight L ell Cs k p*PastWordTimeFields.total L P k p A0 ν :=
      mul_nonneg (timeWeight_nonneg L hell Cs hCs k p ha.1) (PastWordTimeFields.total_nonneg L P k p A0 ν)
    have hb := mul_le_mul_of_nonneg_right (MeanRMSTimeFactors.damping_power_bound hΛ hd hε hε1)
      (mul_nonneg (rpow_nonneg hd.le ((1/2:ℝ)-1)) hB)
    have hp : ((carrier L k).terminal p-q)^(-ε)*((carrier L k).terminal p-q)^((1/2:ℝ)-1)=
        ((carrier L k).terminal p-q)^((1/2:ℝ)-ε-1) := by
      rw [←Real.rpow_add hd]
      congr 1
      ring
    calc
      _=exp (-Λ*((carrier L k).terminal p-q)/4)*
          (((carrier L k).terminal p-q)^((1/2:ℝ)-1)*
            (timeWeight L ell Cs k p*PastWordTimeFields.total L P k p A0 ν)) := by ring
      _≤_ := hb
      _=_ := by rw [←hp];ring
  · simp only [mul_zero,le_refl]

/-- The local span is T-base. No initial age is replaced by its absolute
clock value, and the finite original old-time measure is preserved. -/
theorem damped_old_time_budget (P : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {ell : ℝ} (hell : 0<ell)
    (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ)
    {q A0 ν Λ ε : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hA0 : 0≤A0) (hν : 0≤ν) (hΛ : 0<Λ) (hε : 0≤ε) (hεhalf : ε<1/2) :
    Integrable (fun t=>exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν (anchor k t))
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫ t,exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν (anchor k t)
      ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      ((4:ℝ)^ε*Λ^(-ε))*QuarterRMSTimeFactors.oldTimeBudget P ell Cs k
        (T-R.base) (q-R.base) (1/2-ε) A0 ν := by
  have hb := old_time_budget L P T hT hell Cs hCs k hqbase hqT hTH
    (by linarith : 0<(1/2:ℝ)-ε) (by linarith : (1/2:ℝ)-ε≤1) hA0 hν
  have hcoef : 0≤(4:ℝ)^ε*Λ^(-ε) := mul_nonneg (rpow_nonneg (by norm_num) _) (rpow_nonneg hΛ.le _)
  have hm : Measurable (fun t=>exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν (anchor k t)) := by
    apply Measurable.mul
    · exact ((((carrier L k).terminal_measurable.comp (anchor_measurable k)).sub measurable_const).const_mul (-Λ)).div_const 4 |>.exp
    · exact (totalIntegrand_measurable L P ell Cs k q (1/2:ℝ) A0 ν).comp (anchor_measurable k)
  have hn (t : Fin k→ℝ) : 0≤exp (-Λ*((carrier L k).terminal (anchor k t)-q)/4)*
      totalIntegrand L P ell Cs k q (1/2:ℝ) A0 ν (anchor k t) :=
    mul_nonneg (exp_pos _).le (totalIntegrand_nonneg L P hell Cs hCs k q (1/2:ℝ) A0 ν _)
  have hbound (t : Fin k→ℝ) := damped_integrand_bound L P hell Cs hCs k q A0 ν Λ ε hΛ hε (by linarith) (anchor k t)
  have hi := (hb.1.const_mul ((4:ℝ)^ε*Λ^(-ε))).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun t=>by rw [Real.norm_of_nonneg (hn t)];exact hbound t))
  refine ⟨hi,?_⟩
  have hh := integral_mono hi (hb.1.const_mul ((4:ℝ)^ε*Λ^(-ε))) hbound
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hb.2 hcoef)

end SHE.PastMeanTimeFactors
