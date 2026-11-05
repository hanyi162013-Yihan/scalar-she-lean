module
public import SHE.GirsanovMatchedLocality
public import SHE.PredictableBoundedTruncation
public import SHE.FiniteJointProbabilityLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.GirsanovPastLocality
open MeasureTheory PredictableL2 PastItoInputs Filter Topology Set
open scoped NNReal ENNReal
variable {Ω C:Type}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(Q:Measure Ω)[IsProbabilityMeasure Q](H:ℝ≥0)

theorem event_truncation_tendsto(g:Process (E:=C) 𝓕 Q H)
    (v:ℝ≥0)(A:Set Ω)(hA:MeasurableSet[𝓕 v] A):
    Tendsto (fun n=>eventProcess 𝓕 Q H v A hA
      (PredictableBoundedTruncation.process 𝓕 Q H g Q n)) atTop
      (𝓝 (eventProcess 𝓕 Q H v A hA g)):=by
  let gn:=PredictableBoundedTruncation.process 𝓕 Q H g Q
  have hi:Integrable (fun p=>‖g p‖^2) (energyMeasure Q H):=
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp g)).norm.integrable_sq
  apply PredictableSquareDominatedLimit.tendsto 𝓕 Q H _ _ _ hi
  · intro n
    filter_upwards [eventProcess_ae 𝓕 Q H v A hA (gn n),
      PredictableBoundedTruncation.process_ae 𝓕 Q H g Q n] with p hp hg
    rw [hp]
    by_cases hin:p∈eventAfter v A
    · rw [indicator_of_mem hin,hg]
      exact pow_le_pow_left₀ (norm_nonneg _) (PredictableBoundedTruncation.raw_le 𝓕 Q H g n p) 2
    · rw [indicator_of_notMem hin,norm_zero,zero_pow (by norm_num: (2:ℕ)≠0)]
      exact sq_nonneg _
  · filter_upwards [eventProcess_ae 𝓕 Q H v A hA g] with p hp
    rw [hp]
    by_cases hin:p∈eventAfter v A
    · rw [indicator_of_mem hin]
    · rw [indicator_of_notMem hin,norm_zero,zero_pow (by norm_num: (2:ℕ)≠0)]
      exact sq_nonneg _
  · filter_upwards [ae_all_iff.mpr (fun n=>eventProcess_ae 𝓕 Q H v A hA (gn n)),
      ae_all_iff.mpr (PredictableBoundedTruncation.process_ae 𝓕 Q H g Q),
      eventProcess_ae 𝓕 Q H v A hA g] with p he hg hp
    by_cases hin:p∈eventAfter v A
    · have hh: (fun n=>eventProcess 𝓕 Q H v A hA (gn n) p)=
          (fun n=>PredictableBoundedTruncation.raw 𝓕 Q H g n p):=by
        funext n
        rw [he n,indicator_of_mem hin,hg n]
      rw [hh,hp,indicator_of_mem hin]
      exact PredictableBoundedTruncation.raw_tendsto 𝓕 Q H g p
    · have hh:(fun n=>eventProcess 𝓕 Q H v A hA (gn n) p)=(fun _:ℕ=>(0:C)):=by
        funext n
        rw [he n,indicator_of_notMem hin]
      rw [hh,hp,indicator_of_notMem hin]
      exact tendsto_const_nhds

variable(μ:Measure Ω)[IsProbabilityMeasure μ]
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable(K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 Q H)
variable(T:GirsanovTransportWitness 𝓕 μ Q H J K)
local notation "u"=>T.control
local notation "hT"=>T.transport
variable(hμQ:μ≪Q)(hQμ:Q≪μ)(hlocal:StandardTerminalPastLocality J)
include T hμQ hQμ hlocal in
/-- Deterministic-past locality for every changed-measure L2 input,
derived by bounded two-measure approximation and the original isometry. -/
theorem locality:StandardTerminalPastLocality K:=by
  intro v A hA g
  let gn:=PredictableBoundedTruncation.process 𝓕 Q H g Q
  have hl(n:ℕ):K.integral (eventProcess 𝓕 Q H v A hA (gn n))=ᵐ[Q]
      A.indicator (K.integral (post 𝓕 Q H v (gn n))):=by
    apply GirsanovIntegralTransport.locality_matched 𝓕 μ H Q J K T hμQ hQμ hlocal v A hA
      (PredictableBoundedTruncation.process 𝓕 Q H g μ n) (gn n)
    exact ((Measure.AbsolutelyContinuous.refl (timeMeasure H)).prod hμQ).ae_le (PredictableBoundedTruncation.matched 𝓕 Q H g μ hQμ n)
  have he:=K.integral.continuous.tendsto (eventProcess 𝓕 Q H v A hA g) |>.comp
    (event_truncation_tendsto 𝓕 Q H g v A hA)
  have hp:=K.integral.continuous.tendsto (post 𝓕 Q H v g) |>.comp
    (event_truncation_tendsto 𝓕 Q H g v univ MeasurableSet.univ)
  have hj:=FiniteJointProbabilityLimit.prod Q
    (fun n ω=>K.integral (eventProcess 𝓕 Q H v A hA (gn n)) ω)
    (fun n ω=>K.integral (post 𝓕 Q H v (gn n)) ω)
    (K.integral (eventProcess 𝓕 Q H v A hA g)) (K.integral (post 𝓕 Q H v g))
    (fun n=>(Lp.stronglyMeasurable _).aestronglyMeasurable)
    (fun n=>(Lp.stronglyMeasurable _).aestronglyMeasurable)
    (tendstoInMeasure_of_tendsto_Lp he) (tendstoInMeasure_of_tendsto_Lp hp)
  obtain ⟨ns,hns,hs⟩:=hj.exists_seq_tendsto_ae
  filter_upwards [hs,ae_all_iff.mpr hl] with ω hs hl
  by_cases hω:ω∈A
  · rw [indicator_of_mem hω]
    have heq:(fun n=>K.integral (eventProcess 𝓕 Q H v A hA (gn (ns n))) ω)=
        (fun n=>K.integral (post 𝓕 Q H v (gn (ns n))) ω):=by
      funext n
      simpa only [indicator_of_mem hω] using hl (ns n)
    have hp:=hs.snd_nhds
    rw [←heq] at hp
    exact tendsto_nhds_unique hs.fst_nhds hp
  · rw [indicator_of_notMem hω]
    have heq:(fun n=>K.integral (eventProcess 𝓕 Q H v A hA (gn (ns n))) ω)=(fun _:ℕ=>(0:ℝ)):=by
      funext n
      simpa only [indicator_of_notMem hω] using hl (ns n)
    have he:=hs.fst_nhds
    rw [heq] at he
    exact tendsto_nhds_unique he tendsto_const_nhds
end SHE.GirsanovPastLocality
