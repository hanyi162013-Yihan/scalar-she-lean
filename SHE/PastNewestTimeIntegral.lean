module
public import SHE.PastMeanTimeIntegral
public import SHE.HalfAssignmentIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.PastNewestTimeIntegral
open Set MeasureTheory Real GaussianAssignmentBlocks GaussianFreshAssignments AssignmentGapPartition
  AllocatedAssignmentKernel PhysicalAssignmentGapScale CoveredHistoryGeometry CoveredControlledLaw
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays PhysicalParentGeometry
  PhysicalScoreChain HistoryProductMeasure PhysicalOrderedGaps OrderedGapCoordinates GapSimplexReflection
open scoped BigOperators
open Classical
variable {X:Type}[MeasurableSpace X]{R:ReferenceData}{n:ℕ}(L:Level R X n)

def activeFactor (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(q fresh A0 ν:ℝ)(cs:List (Fin k×Fin (k+1)))(h:History X k):ℝ:=
  if StrictHistory L k h ∧ q<(carrier L k).terminal h then
    ((carrier L k).terminal h-q)^(fresh-1)*timeWeight L ell C k h*
      sqrt |PastMeanTimeFactors.factor L P k h cs A0 ν| else 0

theorem activeFactor_measurable (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(q fresh A0 ν:ℝ)(cs:List (Fin k×Fin (k+1))):
    Measurable (activeFactor L P ell C k q fresh A0 ν cs):=by
  apply Measurable.ite (activeHistory_measurableSet L k q) _ measurable_const
  exact ((((real_rpow_measurable _).comp ((carrier L k).terminal_measurable.sub_const q)).mul
    (FixedHistoryTimeFactors.timeWeight_measurable L ell C k)).mul
      (Real.continuous_sqrt.measurable.comp (continuous_abs.measurable.comp
        (PastMeanTimeFactors.factor_measurable L P k cs A0 ν))))

theorem factor_bound (P:CanonicalCovariance.ProfileParameters){ell:ℝ}(hell:0<ell)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(h:History X k)(hp:StrictHistory L k h)
    {q T A0 ν:ℝ}(hqb:R.base≤q)(hqt:q<(carrier L k).terminal h)
    (hT:initialTerminal L k h≤T)(hA:0≤A0)(hν:0≤ν)
    (cs:List (Fin k×Fin (k+1))):
    timeWeight L ell C k h*sqrt |PastMeanTimeFactors.factor L P k h cs A0 ν|≤
      (scorePrefactor ell C k*sqrt (prefactor P cs A0 n*(T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ))))*
        (∏j,(upper L k h j-lower L k h j)⁻¹)*
          sqrt (gain cs (ν*sqrt (ProfileVariance.upperConstant*(P.lower/2)))
            (P.exponent/4) (fun j=>upper L k h j-lower L k h j)):=by
  let d:Fin k→ℝ:=fun j=>upper L k h j-lower L k h j
  let age:Fin k→ℝ:=fun j=>targets L k h (leafIndex k (fun i=>i) j)-R.base
  let w:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
  have hd(j):0≤d j:=(sub_pos.mpr (lower_lt_upper L k h hp j)).le
  have hg:0≤gain cs w (P.exponent/4) d:=
    Finset.prod_nonneg (fun l _=>gainBlock_nonneg cs (mul_nonneg hν (sqrt_nonneg _)) _ _ hd l)
  have hpf:0≤prefactor P cs A0 n:=prefactor_nonneg P cs hA n
  have hspan:0≤T-R.base:=sub_nonneg.mpr (hqb.trans (hqt.le.trans ((terminal_le_initial L k h).trans hT)))
  have hb:=emptyGain_bound cs (a:=P.exponent/4) (T:=T-R.base)
    (div_nonneg P.exponent_pos.le (by norm_num)) hspan age
      (PastMeanTimeFactors.relative_ages_bounds L k h hp hqb hqt hT)
  have hf:|PastMeanTimeFactors.factor L P k h cs A0 ν|≤
      (prefactor P cs A0 n*(T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ)))*gain cs w (P.exponent/4) d:=by
    rw [abs_of_nonneg (PastMeanTimeFactors.factor_nonneg L P k h hp hqb hqt hA hν cs),
      PastMeanTimeFactors.factor_eq_allocated]
    exact (mul_le_mul_of_nonneg_left hb (mul_nonneg hpf hg)).trans_eq (by unfold emptyCount;ring)
  have hs:=Real.sqrt_le_sqrt hf
  rw [Real.sqrt_mul (mul_nonneg hpf (rpow_nonneg hspan _))] at hs
  have hh:=mul_le_mul_of_nonneg_left hs (timeWeight_nonneg L hell C hC k h hp)
  calc
    _≤timeWeight L ell C k h*(sqrt (prefactor P cs A0 n*(T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ)))*
      sqrt (gain cs w (P.exponent/4) d)):=hh
    _=_:=by rw [timeWeight_eq];dsimp only [d,w];ring

/-- The repaired fresh collision and half old BLOCK-MINIMUM gains are
integrable under the original restricted old-time product measure. -/
theorem actual_assignment_integral_bound (P:CanonicalCovariance.ProfileParameters)
    (T:ℝ)(hT:∀x,L.terminal x=T){ell:ℝ}(hell:0<ell)(C:ℕ→ℝ)(hC:∀j,0≤C j)
    (k:ℕ)(x:X)(z:Fin k→StoppedFourier.HeatCircle){q fresh A0 ν:ℝ}
    (hqb:R.base≤q)(hqT:q<T)(hTH:T≤R.horizon)(hf:0<fresh)(hf1:fresh≤1)
    (hA:0≤A0)(hν:0≤ν)(cs:List (Fin k×Fin (k+1)))
    (hc:cs∈assignments (m:=k+1) (List.finRange k)):
    let w:=ν*sqrt (ProfileVariance.upperConstant*(P.lower/2))
    let p:Fin (k+1)→ℝ:=Fin.cons fresh (fun i=>holderDegree cs hc (P.exponent/4) i/2)
    let K:=scorePrefactor ell C k*sqrt (prefactor P cs A0 n*(T-R.base)^((P.exponent/4)*(emptyCount cs:ℝ)))
    Integrable (fun t=>activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z)))
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫t,activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z))
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)))≤
      K*(max 1 w)^((k:ℝ)/2)*(((k+1:ℕ):ℝ)^2/(T-q)*∏i,(T-q)^(p i)/(p i)):=by
  intro w p K
  let μt:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let Fd:(Fin k→ℝ)→ℝ:=fun d=>(slack (T-q) d)^(fresh-1)*(∏i,(d i)⁻¹)*sqrt (gain cs w (P.exponent/4) d)
  let G:(Fin k→ℝ)→ℝ:=fun t=>if StrictHistory L k (separated k (x,t,z)) ∧
    q<(carrier L k).terminal (separated k (x,t,z)) then Fd (gaps T k t) else 0
  have ha:0<P.exponent/4:=div_pos P.exponent_pos (by norm_num)
  have ha1:P.exponent/4≤1:=by linarith [P.exponent_le_one]
  have hw:0≤w:=mul_nonneg hν (sqrt_nonneg _)
  have hh:=halfDensity_integral_bound cs hc hw ha ha1 hf hf1 (sub_pos.mpr hqT)
  have he:(fun d:Fin k→ℝ=>if (∀i,0<d i) ∧ (∑i,d i)<T-q then Fd d else 0)=
      halfDensity cs w (P.exponent/4) fresh (T-q):=by
    funext d
    simp only [Fd,halfDensity,GapSimplexFaces.simplex,slack,sub_pos]
  have hGi:Integrable G μt:=by
    apply (active_gap_integrable_iff L T hT q hqb hTH k x z Fd).mpr
    rw [he]
    exact hh.1
  have hGval:(∫t,G t ∂μt)=∫d,halfDensity cs w (P.exponent/4) fresh (T-q) d:=by
    change (∫t,if StrictHistory L k (separated k (x,t,z)) ∧
      q<(carrier L k).terminal (separated k (x,t,z)) then Fd (gaps T k t) else 0 ∂μt)=_
    rw [active_gap_integral L T hT q hqb hTH,he]
  have hK:0≤K:=mul_nonneg (scorePrefactor_nonneg hell C hC k) (sqrt_nonneg _)
  have hdom(t:Fin k→ℝ):activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z))≤K*G t:=by
    by_cases ht:StrictHistory L k (separated k (x,t,z)) ∧ q<(carrier L k).terminal (separated k (x,t,z))
    · have hinit:initialTerminal L k (separated k (x,t,z))≤T:=by simp only [initialTerminal,root_separated,hT,le_refl]
      have hb:=factor_bound L P hell C hC k _ ht.1 hqb ht.2 hinit hA hν cs
      have hgap:=old_gaps_eq L T hT k t x z ht.1
      have hfr:(carrier L k).terminal (separated k (x,t,z))-q=slack (T-q) (gaps T k t):=by
        rw [terminal_eq_boundary L T hT k t x z ht.1]
        simp only [slack,sum_gaps]
        ring
      dsimp only [activeFactor,G]
      rw [if_pos ht,if_pos ht]
      have hm:=mul_le_mul_of_nonneg_left hb (rpow_nonneg (sub_pos.mpr ht.2).le (fresh-1))
      rw [hgap,hfr] at hm
      have hgap'(j):upper L k (separated k (x,t,z)) j-lower L k (separated k (x,t,z)) j=gaps T k t j:=congrFun hgap j
      simp_rw [hgap'] at hm
      rw [hfr]
      dsimp only [K,Fd,w] at hm ⊢
      convert! hm using 1 <;> ring
    · simp only [activeFactor,G,if_neg ht,mul_zero,le_refl]
  have hn(t:Fin k→ℝ):0≤activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z)):=by
    unfold activeFactor
    split_ifs with ht
    · exact mul_nonneg (mul_nonneg (rpow_nonneg (sub_pos.mpr ht.2).le _)
        (timeWeight_nonneg L hell C hC k _ ht.1)) (sqrt_nonneg _)
    · exact le_rfl
  have hs:Measurable (fun t:Fin k→ℝ=>separated k (x,t,z)):=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hi:Integrable (fun t=>activeFactor L P ell C k q fresh A0 ν cs (separated k (x,t,z))) μt:=
    (hGi.const_mul K).mono' ((activeFactor_measurable L P ell C k q fresh A0 ν cs).comp hs).aestronglyMeasurable
      (ae_of_all _ (fun t=>by rw [Real.norm_of_nonneg (hn t)];exact hdom t))
  refine ⟨hi,?_⟩
  calc
    _≤∫t,K*G t ∂μt:=integral_mono hi (hGi.const_mul K) hdom
    _=K*(∫d,halfDensity cs w (P.exponent/4) fresh (T-q) d):=by rw [integral_const_mul,hGval]
    _≤_:=by convert! mul_le_mul_of_nonneg_left hh.2 hK using 1 <;> ring

end SHE.PastNewestTimeIntegral
