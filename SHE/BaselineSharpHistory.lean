module

public import SHE.BaselineScaleParentInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.BaselineSharpHistory
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2
  ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates OrderedHeatForests
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays CoveredControlledLaw
  CoveredHistoryGeometry PhysicalParentGeometry BaselineAssignmentScale
open scoped BigOperators
local instance baselineSharpHistory_periodPos : Fact (0<2*π) := ⟨by positivity⟩

/-- A genuine AE time property pulls back to ALL original history
nodes on strict histories. Clipped endpoints are never substituted into
an AE time statement. -/
theorem history_of_time_ae {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
    (L : Level R X n) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (Q : ℝ→Prop) (hQ : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),Q r) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R ρ k,StrictHistory L k p →
      ∀ j : Fin k,Q (lower L k p j) := by
  have hQt : ∀ᵐ r ∂volume.restrict (Ioc R.base R.horizon),Q r := by
    rw [ae_restrict_iff' measurableSet_Ici] at hQ
    filter_upwards [ae_restrict_of_ae hQ,ae_restrict_mem measurableSet_Ioc] with r hr hrbox
    exact hr (R.base_nonneg.trans hrbox.1.le)
  have hnode : ∀ᵐ z ∂nodeMeasure R,Q z.1 :=
    Measure.quasiMeasurePreserving_fst.ae hQt
  induction k with
  | zero => exact ae_of_all _ (fun _ _ j=>Fin.elim0 j)
  | succ k ih =>
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ih,
      Measure.quasiMeasurePreserving_snd.ae hnode] with p hp hn
    intro hstrict j
    refine Fin.cases ?_ (fun i=>?_) j
    · have ht : (carrier L k).nodeTime p=p.2.1 :=
        ClippedCovariance.clip_eq ⟨hstrict.2.1.le,hstrict.2.2.le⟩
      change Q p.2.1 at hn
      simpa only [lower,Fin.cases_zero,ht] using hn
    · exact hp hstrict.1 i

/-- One common parameter event works for EVERY actual finite level.
All profile baseline derivative L2 estimates are therefore applicable
at the actual old times without an uncountable AE diagonal inference. -/
theorem ae_history_sharp_all_levels (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2) :
    ∀ᵐ θ ∂volume,∀ (X : Type) [MeasurableSpace X] (R : ReferenceData) (n : ℕ)
      (L : Level R X n) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ),
      ∀ᵐ p ∂CutoffWordHistories.historyMeasure R ρ k,StrictHistory L k p →
        ∀ j : Fin k,normTwo haarAddCircle (fun x=>ControlledProfile.derivative P Λ u d
          ((targets L k p (leafIndex k (fun i=>i) j),x),θ))≤
          sharpConstant P d*(targets L k p (leafIndex k (fun i=>i) j))^((P.exponent-1)/4) := by
  filter_upwards [ae_derivative_sharp_power P hΛ u d hsmallPoint hsmallL2] with θ hθ
  intro X inst R n L ρ instρ k
  filter_upwards [history_of_time_ae L ρ k (fun r=>normTwo haarAddCircle
    (fun x=>ControlledProfile.derivative P Λ u d ((r,x),θ))≤sharpConstant P d*r^((P.exponent-1)/4)) hθ]
      with p hp
  intro hstrict j
  have ht : targets L k p (leafIndex k (fun i=>i) j)=lower L k p j := by
    rw [targets,CoveredHistoryGeometry.leaf_observation L k p j]
  simpa only [ht] using hp hstrict j

end SHE.BaselineSharpHistory
