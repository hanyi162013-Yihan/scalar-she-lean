module

public import SHE.WeightedQuarterSpatialEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.WeightedQuarterSpatialEvent
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure ActualMeanKernel
  ScalarMeanEnvelope NormalizedKernelSplit HistoryQuarterFields QuarterSpatialEvent
local instance weightedQuarterSpatialSections_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

/-- Convert the actual root/time/input spatial moment event into a
genuine joint input/output estimate for almost every old-time section.
All exchanges use joint Borel events; the sharp time amplitude remains
one deterministic scalar in each section. -/
theorem normalized_time_sections (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T A Λ : ℝ) (hT : ∀ p,L.terminal p=T)
    (hA : ∀ p,(L.observations.observations p 0).target=A)
    (hx : ∀ p,(L.observations.observations p 0).center=p)
    (Q : CanonicalCovariance.ProfileParameters) (k : ℕ) (q Cf ell A0 ν C : ℝ)
    (hCf : 0 ≤ Cf) (hell : 0 < ell) (hC : 0 ≤ C) (Cs : ℕ → ℝ) (hCs : ∀ j,0 ≤ Cs j)
    (m : Ω → History HeatCircle k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2)) (N : ℕ)
    (hspatial : ∀ᵐ p : HeatCircle ∂AddCircle.haarAddCircle,
      ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
        let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
        let r := rowTime L k q p₀
        ∀ hp : StrictHistory L k p₀,q < (carrier L k).terminal p₀ →
          ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
            (∫ ω,‖weightedSpatial L k Λ q r m t ω y p‖^N ∂μ) ≤
              C*((Real.sqrt (Cf/(ell*((carrier L k).terminal p₀-r)))*
                SharpWordTimeScale.total L Q k p₀ q A0 ν)*
                  massBudget L k p₀ (timeWeight L ell Cs k p₀) r y)^N) :
    ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
      active L T k q t →
        ∀ᵐ z : Space ∂(AddCircle.haarAddCircle (T:=2*Real.pi)).prod AddCircle.haarAddCircle,
          timeMoment L μ T Λ k q m N (t,z) ≤
            C*(heatEnvelope (amplitude L Q k q Cf ell A0 ν Cs t)
              (quarterTraceTime (R:=R) T k q t) (A-q) z)^N := by
  let F : HeatCircle × ((Fin k → ℝ) × HeatCircle) → Prop := fun z =>
    active L T k q z.2.1 → timeMoment L μ T Λ k q m N (z.2.1,(z.2.2,z.1)) ≤
      C*(heatEnvelope (amplitude L Q k q Cf ell A0 ν Cs z.2.1)
        (quarterTraceTime (R:=R) T k q z.2.1) (A-q) (z.2.2,z.1))^N
  have hF : MeasurableSet {z | F z} :=
    (moment_event_measurableSet L μ T A Λ Q k q Cf ell A0 ν C Cs m hm N).preimage
      (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  have htarget (p : HeatCircle) (i : Fin 1) : (L.observations.observations p i).target=(fun _ => A) i := by
    have hi : i=0 := Subsingleton.elim _ _
    simpa only [hi] using hA p
  have hroot : ∀ᵐ p : HeatCircle ∂AddCircle.haarAddCircle,
      ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
        ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,F (p,t,y) := by
    filter_upwards [hspatial] with p hp
    filter_upwards [hp] with t ht
    by_cases ha : active L T k q t
    · let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
      have hstrict : StrictHistory L k p₀ :=
        (FixedHistoryTimeFactors.strict_sections L T hT k t p 0 (fun _ => 0) (fun _ => 0)).mpr ha.1
      have hq : q < (carrier L k).terminal p₀ := by
        simpa only [p₀,terminal_separated L T hT] using ha.2
      have hTA : fixedTerminal (R:=R) T k t ≤ A := by
        rw [←terminal_separated L T hT k t (0:HeatCircle) (fun _ => (0:HeatCircle))]
        exact (terminal_le_initial L k _).trans ((L.targets_after _ 0).trans (le_of_eq (hA _)))
      have hW : 0 ≤ timeWeight L ell Cs k (anchor k t) :=
        timeWeight_nonneg L hell Cs hCs k (anchor k t) ha.1
      have hD := SharpWordTimeScale.total_nonneg L Q k (anchor k t) q A0 ν
      have hd := SharpWordTimeScale.total_sections L T hT Q (fun _ => A) htarget k t p 0
        (fun _ => 0) (fun _ => 0) q A0 ν
      have hw := FixedHistoryTimeFactors.timeWeight_sections L T hT ell Cs k t p 0
        (fun _ => 0) (fun _ => 0)
      filter_upwards [ht hstrict hq] with y hy
      intro _
      have hrow : rowTime L k q p₀=quarterRowTime (R:=R) T k q t :=
        rowTime_separated L T hT k q t p (fun _ => 0)
      have hh := quarter_massBudget_bound L T A hT hA hx k q t p y ha.2 hTA
        Cf ell (SharpWordTimeScale.total L Q k (anchor k t) q A0 ν)
          (timeWeight L ell Cs k (anchor k t)) hCf hell hD hW
      have hs := (quarter_widths (R:=R) ha.2 hTA).1
      have hn : 0 ≤ (Real.sqrt (Cf/(ell*((carrier L k).terminal p₀-quarterRowTime (R:=R) T k q t)))*
          SharpWordTimeScale.total L Q k (anchor k t) q A0 ν)*
            massBudget L k p₀ (timeWeight L ell Cs k (anchor k t)) (quarterRowTime (R:=R) T k q t) y := by
        rw [massBudget_scalar L A hA hx]
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hD)
          (mul_nonneg (mul_nonneg (massCoefficient_nonneg k hW) (Real.rpow_nonneg hs.le _)) (norm_nonneg _))
      have hy' : timeMoment L μ T Λ k q m N (t,(y,p)) ≤
          C*((Real.sqrt (Cf/(ell*((carrier L k).terminal p₀-quarterRowTime (R:=R) T k q t)))*
            SharpWordTimeScale.total L Q k (anchor k t) q A0 ν)*
              massBudget L k p₀ (timeWeight L ell Cs k (anchor k t)) (quarterRowTime (R:=R) T k q t) y)^N := by
        simpa only [timeMoment,←hrow,hd,hw,p₀,anchor] using hy
      exact hy'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hh N) hC)
    · exact ae_of_all _ (fun _ h => False.elim (ha h))
  have hswap := ae_parameter_swap (AddCircle.haarAddCircle (T:=2*Real.pi))
    (Measure.pi (fun _ : Fin k => volume.restrict (Ioc R.base R.horizon))) AddCircle.haarAddCircle F hF hroot
  filter_upwards [hswap] with t ht
  intro ha
  have hFt : MeasurableSet {z : HeatCircle × HeatCircle | F (z.1,t,z.2)} :=
    hF.preimage (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hjoint := (Measure.ae_prod_iff_ae_ae hFt).mpr ht
  have hswapMP : MeasurePreserving (Prod.swap : Space → Space)
      ((AddCircle.haarAddCircle (T:=2*Real.pi)).prod AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle (T:=2*Real.pi)).prod AddCircle.haarAddCircle) :=
    Measure.measurePreserving_swap
  filter_upwards [hswapMP.quasiMeasurePreserving.ae hjoint] with z hz
  exact hz ha

end SHE.WeightedQuarterSpatialEvent
