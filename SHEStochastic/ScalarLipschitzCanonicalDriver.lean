module

public import SHEStochastic.CanonicalNativeBrownian
public import SHEStochastic.NativeBrownianPathLaw
public import SHEStochastic.RandomInitialBrownianFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzCanonicalDriver
open MeasureTheory Set Filter SHE ProbabilityTheory
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal Topology

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H I)

abbrev DriverSpace (I : Type*) (H : ℝ≥0) := CanonicalContinuousStateDriver.Space (E := ℝ) (ι := I) H

/-- Use a deterministic dummy state so the canonical sample carries
only the given Brownian paths. No law of a competing solution enters. -/
def bundle : Ω → DriverSpace I H :=
  CanonicalNativeBrownian.bundle F μ H P (fun _ _ => (0 : ℝ)) (fun _ => continuous_const)

theorem bundle_measurable : Measurable (bundle P) :=
  CanonicalNativeBrownian.measurable_bundle F μ H P _ _ (fun _ => measurable_const)

def law : Measure (DriverSpace I H) := μ.map (bundle P)

instance law_probability : IsProbabilityMeasure (law P) := by
  constructor
  rw [law,Measure.map_apply (bundle_measurable P) MeasurableSet.univ,preimage_univ,measure_univ]

theorem law_eq {Ξ : Type*} [MeasurableSpace Ξ]
    {G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›} {η : Measure Ξ} [IsProbabilityMeasure η]
    (Q : FiniteScalarIto.Family G η H I) : law P=law Q := by
  let ϕ (x : I → C(Icc (0 : ℝ) (H : ℝ),ℝ)) : DriverSpace I H := (0,x)
  have hϕ : Measurable ϕ := measurable_const.prodMk measurable_id
  have hP : bundle P=ϕ ∘ BrownianFuturePath.value P.W P.continuous 0 H := rfl
  have hQ : bundle Q=ϕ ∘ BrownianFuturePath.value Q.W Q.continuous 0 H := rfl
  rw [law,law,hP,hQ,←Measure.map_map hϕ (BrownianFuturePath.measurable F P.W P.continuous P.adapted 0 H),
    ←Measure.map_map hϕ (BrownianFuturePath.measurable G Q.W Q.continuous Q.adapted 0 H),
    NativeBrownianPathLaw.map_eq P Q]

def rawFamily : FiniteScalarIto.Family (filtration (E := ℝ) (ι := I) H) (law P) H I where
  W := coordinate H
  adapted := coordinate_adapted H
  continuous := coordinate_continuous H
  law n a := CanonicalNativeBrownian.law F μ H P _ _ (fun _ => measurable_const) n a

local notation "ρ" => (Measure.dirac () : Measure Unit)

abbrev Completed (H : ℝ≥0) (η : Measure (DriverSpace I H)) :=
  RandomInitialBrownianFamily.Space ρ η

def completedFamily (η : Measure (DriverSpace I H)) [IsProbabilityMeasure η]
    (R : FiniteScalarIto.Family (filtration (E := ℝ) (ι := I) H) η H I) :
    FiniteScalarIto.Family
      (RandomInitialBrownianFamily.filtration ρ η (filtration (E := ℝ) (ι := I) H))
      (IndependentNoiseCompletion.measure ρ η) H I :=
  RandomInitialBrownianFamily.family ρ η (filtration (E := ℝ) (ι := I) H) H R

theorem past_measurable (t : ℝ≥0) :
    Measurable[F t] ((history (E := ℝ) (ι := I) H t) ∘ bundle P) :=
  (CanonicalNativeBrownian.past_adapted_capped F μ H P _ _ (fun _ => measurable_const) t).mono
    (F.mono (min_le_left _ _)) le_rfl

def pull (η : Measure (DriverSpace I H)) (ω : Ω) : Completed H η := ((),bundle P ω)

theorem pull_raw_preserving (η : Measure (DriverSpace I H)) (hη : law P=η) :
    @MeasurePreserving Ω (Unit×DriverSpace I H) _ _ (pull P η) μ ((ρ).prod η) := by
  let _ : IsProbabilityMeasure η := hη ▸ law_probability P
  have hb := bundle_measurable P
  have hC : Measurable (Prod.mk () : DriverSpace I H → Unit×DriverSpace I H) :=
    measurable_const.prodMk measurable_id
  refine ⟨hC.comp hb,?_⟩
  change μ.map ((Prod.mk ()) ∘ bundle P)=(ρ).prod η
  rw [←Measure.map_map hC hb,show μ.map (bundle P)=η from hη,Measure.dirac_prod]

theorem pull_preserving (η : Measure (DriverSpace I H)) (hη : law P=η)
    (hn : NullCompleteFiltration.ContainsNullSets F μ) :
    MeasurePreserving (pull P η) μ (IndependentNoiseCompletion.measure ρ η) := by
  have hP := pull_raw_preserving P η hη
  have hm : @Measurable Ω (Completed H η) _
      (@NullMeasurableSpace.instMeasurableSpace (Unit×DriverSpace I H) inferInstance ((ρ).prod η))
      (pull P η) := by
    intro A hA
    have hNA : @NullMeasurableSet (Unit×DriverSpace I H)
        (inferInstanceAs (MeasurableSpace (Unit×DriverSpace I H))) A ((ρ).prod η) := hA
    have hN : NullMeasurableSet ((pull P η) ⁻¹' A) μ :=
      hNA.preimage hP.quasiMeasurePreserving
    let _ : μ.IsComplete := ⟨fun s hs => F.le 0 _ (hn 0 s hs)⟩
    exact hN.measurable_of_complete
  refine ⟨hm,?_⟩
  ext A hA
  rw [Measure.map_apply hm hA]
  have hNA : @NullMeasurableSet (Unit×DriverSpace I H)
      (inferInstanceAs (MeasurableSpace (Unit×DriverSpace I H))) A ((ρ).prod η) := hA
  exact hP.measure_preimage hNA

theorem pull_filtered (η : Measure (DriverSpace I H)) (hη : law P=η)
    (hn : NullCompleteFiltration.ContainsNullSets F μ) (t : ℝ≥0) :
    @Measurable Ω (Completed H η) (F t)
      (RandomInitialBrownianFamily.filtration ρ η (filtration (E := ℝ) (ι := I) H) t)
      (pull P η) := by
  have hP := pull_raw_preserving P η hη
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (pull P η)
    ((IndependentNoiseProduct.filtration RandomInitialBrownianFamily.initialFiltration
      (filtration (E := ℝ) (ι := I) H)) t⊔IndependentNoiseCompletion.nullSigma ρ η) ≤ F t
  rw [MeasurableSpace.comap_sup]
  apply sup_le
  · apply Measurable.comap_le
    change @Measurable Ω (Unit×DriverSpace I H) (F t)
      ((inferInstance : MeasurableSpace Unit).prod (filtration (E := ℝ) (ι := I) H t)) (pull P η)
    have hh : @Measurable Ω (DriverSpace I H) (F t) (filtration (E := ℝ) (ι := I) H t) (bundle P) := by
      rw [measurable_iff_comap_le]
      change MeasurableSpace.comap (bundle P) (MeasurableSpace.comap (history H t) inferInstance)≤F t
      rw [MeasurableSpace.comap_comp]
      exact (past_measurable P t).comap_le
    exact measurable_const.prodMk hh
  · apply MeasurableSpace.comap_le_iff_le_map.mpr
    apply MeasurableSpace.generateFrom_le
    intro A hA
    change MeasurableSet[F t] ((pull P η) ⁻¹' A)
    apply hn t
    rw [hP.measure_preimage (NullMeasurableSet.of_null hA)]
    exact hA

omit [Countable I] [IsProbabilityMeasure μ] in
/-- The exact pullback driver is the original one centered at zero and
clamped outside the time horizon. -/
theorem coordinate_pull (η : Measure (DriverSpace I H)) (i : I) (t : ℝ≥0) (ω : Ω) :
    coordinate H i t (pull P η ω).2 = P.W i (min t H) ω-P.W i 0 ω := by
  change P.W i (0+(clock H t).val.toNNReal) ω-P.W i 0 ω=_
  have hc : (clock H t).val.toNNReal=min t H := by
    change (min (t : ℝ) (H : ℝ)).toNNReal=min t H
    rw [←NNReal.coe_min,Real.toNNReal_coe]
  rw [hc,zero_add]

end SHEStochastic.ScalarLipschitzCanonicalDriver
