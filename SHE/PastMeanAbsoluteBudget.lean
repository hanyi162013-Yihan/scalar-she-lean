module

public import SHE.PastMeanDampedTime
public import SHE.PastMeanSections
public import SHE.ParentMeanMass
public import SHE.HistorySpatialSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastMeanTimeFactors
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalParentGeometry HistoryProductMeasure QuarterSpatialEvent
local instance pastMeanAbsoluteBudget_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)

theorem totalIntegrand_sections (P : CanonicalCovariance.ProfileParameters) (T : ℝ)
    (hT : ∀ x,L.terminal x=T) (hTarget : ∀ x i,(L.observations.observations x i).target=T)
    (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (q fresh A0 ν : ℝ)
    (t : Fin k→ℝ) (x : HeatCircle) (z : Fin k→HeatCircle) :
    totalIntegrand L P ell Cs k q fresh A0 ν (separated k (x,t,z))=
      totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t) := by
  change totalIntegrand L P ell Cs k q fresh A0 ν (separated k (x,t,z))=
    totalIntegrand L P ell Cs k q fresh A0 ν (separated k ((0:HeatCircle),t,fun _=>0))
  have hs:=FixedHistoryTimeFactors.strict_sections L T hT k t x (0:HeatCircle) z (fun _=>0)
  have ht:=ActualMeanKernel.terminal_separated L T hT k t x z
  have ht0:=ActualMeanKernel.terminal_separated L T hT k t (0:HeatCircle) (fun _=>0)
  unfold totalIntegrand
  rw [ht,ht0,hs]
  rw [FixedHistoryTimeFactors.timeWeight_sections L T hT ell Cs k t x (0:HeatCircle) z (fun _=>0),
    PastWordTimeFields.total_sections L P T hT (fun _=>T) hTarget k t x (0:HeatCircle) z (fun _=>0)]

def absoluteDensity (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) (p : History HeatCircle k) : ℝ :=
  totalIntegrand L P ell Cs k q fresh A0 ν p*ParentMeanDensity.parentProduct L k p

theorem absoluteDensity_nonneg (P : CanonicalCovariance.ProfileParameters) {ell : ℝ} (hell : 0<ell)
    (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ) (q fresh A0 ν : ℝ) (p : History HeatCircle k) :
    0≤absoluteDensity L P ell Cs k q fresh A0 ν p:=mul_nonneg
      (totalIntegrand_nonneg L P hell Cs hCs k q fresh A0 ν p) (ParentMeanDensity.parentProduct_nonneg L k p)

theorem absoluteDensity_measurable (P : CanonicalCovariance.ProfileParameters) (ell : ℝ) (Cs : ℕ→ℝ)
    (k : ℕ) (q fresh A0 ν : ℝ) : Measurable (absoluteDensity L P ell Cs k q fresh A0 ν):=
  (totalIntegrand_measurable L P ell Cs k q fresh A0 ν).mul (ParentMeanDensity.parentProduct_measurable L k)

/-- All original insertion locations are integrated absolutely. Only
the finite parent-assignment count is paid; time densities are not squared. -/
theorem absoluteDensity_space_mass (P : CanonicalCovariance.ProfileParameters) (T : ℝ)
    (hT : ∀ x,L.terminal x=T) (hTarget : ∀ x i,(L.observations.observations x i).target=T)
    (hages : ∀ x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target)
    (ell : ℝ) (Cs : ℕ→ℝ) (k : ℕ) (q fresh A0 ν : ℝ) (t : Fin k→ℝ) (x : HeatCircle) :
    Integrable (fun z=>absoluteDensity L P ell Cs k q fresh A0 ν (separated k (x,t,z)))
      (Measure.pi (fun _ : Fin k=>haarAddCircle)) ∧
    (∫ z,absoluteDensity L P ell Cs k q fresh A0 ν (separated k (x,t,z))
      ∂Measure.pi (fun _ : Fin k=>haarAddCircle))=
        totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t)*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ) := by
  classical
  let I:=totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t)
  by_cases ha : active L T k q t
  · let p0:=separated k (x,t,fun _=>(0:HeatCircle))
    have hp : StrictHistory L k p0:=
      (FixedHistoryTimeFactors.strict_sections L T hT k t x (0:HeatCircle) (fun _=>0) (fun _=>0)).mpr ha.1
    have he (z : Fin k→HeatCircle) : absoluteDensity L P ell Cs k q fresh A0 ν (separated k (x,t,z))=
        I*parentEnvelope L hages k p0 hp z := by
      rw [absoluteDensity,totalIntegrand_sections L P T hT hTarget ell Cs k q fresh A0 ν t x z]
      rw [show separated k (x,t,z)=replaceSpace k p0 z from (replaceSpace_separated k x t (fun _=>0) z).symm,
        ParentMeanDensity.parentProduct_replaceSpace_eq L hages k p0 hp z]
    simp_rw [he]
    refine ⟨((parentEnvelope_continuous L hages k p0 hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul I,?_⟩
    rw [integral_const_mul,parentEnvelope_mass L hages k p0 hp]
  · have hi : I=0:=by
      unfold I totalIntegrand
      have ht: (carrier L k).terminal (anchor k t)=ActualMeanKernel.fixedTerminal (R:=R) T k t:=
        ActualMeanKernel.terminal_separated L T hT k t (0:HeatCircle) (fun _=>0)
      rw [ht]
      unfold active at ha
      exact ite_eq_right ha
    have he (z : Fin k→HeatCircle) : absoluteDensity L P ell Cs k q fresh A0 ν (separated k (x,t,z))=0:=by
      rw [absoluteDensity,totalIntegrand_sections L P T hT hTarget ell Cs k q fresh A0 ν t x z]
      change I*_=0
      rw [hi,zero_mul]
    refine ⟨?_,?_⟩
    · simpa only [he] using (integrable_const (0:ℝ) : Integrable (fun _ : Fin k→HeatCircle=>(0:ℝ)) (Measure.pi (fun _ : Fin k=>haarAddCircle)))
    · simp_rw [he]
      rw [integral_zero]
      change 0=I*_
      rw [hi,zero_mul]

/-- Genuine absolute original-history L1 mass with its exact local
relative-age old-time budget. This supplies Fubini before cancellations. -/
theorem absoluteDensity_history_budget (P : CanonicalCovariance.ProfileParameters) (T : ℝ)
    (hT : ∀ x,L.terminal x=T) (hTarget : ∀ x i,(L.observations.observations x i).target=T)
    (hages : ∀ x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target)
    {ell : ℝ} (hell : 0<ell) (Cs : ℕ→ℝ) (hCs : ∀ j,0≤Cs j) (k : ℕ)
    {q fresh A0 ν : ℝ} (hqbase : R.base≤q) (hqT : q<T) (hTH : T≤R.horizon)
    (hf : 0<fresh) (hf1 : fresh≤1) (hA0 : 0≤A0) (hν : 0≤ν)
    (root : Measure HeatCircle) [IsFiniteMeasure root] :
    Integrable (absoluteDensity L P ell Cs k q fresh A0 ν) (historyMeasure R root k) ∧
      (∫ p,absoluteDensity L P ell Cs k q fresh A0 ν p ∂historyMeasure R root k)≤
        root.real univ*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
          QuarterRMSTimeFactors.oldTimeBudget P ell Cs k (T-R.base) (q-R.base) fresh A0 ν := by
  let τ:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc R.base R.horizon))
  let σ:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*Real.pi))
  let G:=absoluteDensity L P ell Cs k q fresh A0 ν
  let B:=fun t=>totalIntegrand L P ell Cs k q fresh A0 ν (anchor k t)
  let N:=(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)
  have hB:=old_time_budget L P T hT hell Cs hCs k hqbase hqT hTH hf hf1 hA0 hν
  have hGm : Measurable G:=absoluteDensity_measurable L P ell Cs k q fresh A0 ν
  have hGn (p) : 0≤G p:=absoluteDensity_nonneg L P hell Cs hCs k q fresh A0 ν p
  have hm : Measurable (fun z : HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>G (separated k z)):=
    hGm.comp (separated_measurable k)
  have hs (x : HeatCircle) (t : Fin k→ℝ):=absoluteDensity_space_mass L P T hT hTarget hages ell Cs k q fresh A0 ν t x
  have hinner (x : HeatCircle) : Integrable (fun z : (Fin k→ℝ)×(Fin k→HeatCircle)=>G (separated k (x,z))) (τ.prod σ) := by
    apply (integrable_prod_iff ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr
    refine ⟨ae_of_all _ (fun t=>(hs x t).1),?_⟩
    have he : (fun t=>∫ z,‖G (separated k (x,t,z))‖ ∂σ)=fun t=>B t*N:=by
      funext t
      simp_rw [Real.norm_of_nonneg (hGn _)]
      exact (hs x t).2
    change Integrable (fun t=>∫ z,‖G (separated k (x,t,z))‖ ∂σ) τ
    rw [he]
    exact hB.1.mul_const N
  have hmass (x : HeatCircle) : (∫ z : (Fin k→ℝ)×(Fin k→HeatCircle),G (separated k (x,z)) ∂τ.prod σ)=
      (∫ t,B t ∂τ)*N := by
    rw [integral_prod _ (hinner x)]
    change (∫ t,∫ z,G (separated k (x,t,z)) ∂σ ∂τ)=(∫ t,B t ∂τ)*N
    calc
      _=(∫ t,B t*N ∂τ):=integral_congr_ae (ae_of_all _ (fun t=>(hs x t).2))
      _=_:=integral_mul_const _ _
  have hfull : Integrable (fun z : HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>G (separated k z))
      (root.prod (τ.prod σ)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hinner,?_⟩
    have he : (fun x=>∫ z,‖G (separated k (x,z))‖ ∂τ.prod σ)=fun _ : HeatCircle=>(∫ t,B t ∂τ)*N:=by
      funext x
      simp_rw [Real.norm_of_nonneg (hGn _)]
      exact hmass x
    rw [he]
    exact integrable_const _
  have hmp:=separated_measurePreserving R root k
  have hi : Integrable G (historyMeasure R root k):=
    (hmp.integrable_comp hGm.aestronglyMeasurable).mp hfull
  refine ⟨hi,?_⟩
  have he : (∫ p,G p ∂historyMeasure R root k)=
      root.real univ*N*(∫ t,B t ∂τ) := by
    rw [←hmp.map_eq,integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq];exact hGm.aestronglyMeasurable)]
    rw [integral_prod _ hfull]
    simp_rw [hmass]
    rw [integral_const]
    simp only [smul_eq_mul]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hB.2 (mul_nonneg measureReal_nonneg (Nat.cast_nonneg _))

end SHE.PastMeanTimeFactors
