module

public import SHE.BaselineSharpHistory
public import SHE.HistoryRelativeSections
public import SHE.FixedHistoryDomain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.BaselineSharpHistory
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2
  ProfilePointwise ProfileStability ControlledProfile ControlledScoreRates OrderedHeatForests
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays CoveredControlledLaw
  CoveredHistoryGeometry PhysicalParentGeometry BaselineAssignmentScale HistoryProductMeasure
open scoped BigOperators
local instance baselineSharpSections_periodPos : Fact (0<2*π) := ⟨by positivity⟩

/-- The sharp native-leaf baseline property descends to a COMMON old-time
section. The zero anchor is justified by literal time-array invariance,
not by evaluating an AE history assertion at a chosen spatial point. -/
theorem ae_sharp_time_sections (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ}
    (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2) :
    ∀ᵐ θ ∂volume,∀ (R : ReferenceData) (n : ℕ) (L : Level R HeatCircle n)
      (T : ℝ),(∀ x,L.terminal x=T) → ∀ k : ℕ,
      ∀ᵐ t : Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)),
        let a := separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
        StrictHistory L k a → ∀ j : Fin k,
          normTwo haarAddCircle (fun x=>ControlledProfile.derivative P Λ u d
            ((targets L k a (leafIndex k (fun i=>i) j),x),θ))≤
            sharpConstant P d*(targets L k a (leafIndex k (fun i=>i) j))^((P.exponent-1)/4) := by
  filter_upwards [ae_history_sharp_all_levels P hΛ u d hsmallPoint hsmallL2] with θ hθ
  intro R n L T hT k
  have hsec := ae_relative_spatial_sections R k (hθ HeatCircle R n L haarAddCircle k)
  filter_upwards [hsec] with t ht
  intro a hp
  obtain ⟨x,hx⟩ := ht.exists
  obtain ⟨w,hw⟩ := hx.exists
  let p := separated k (x,t,fun i=>w i+x)
  have hpp : StrictHistory L k p :=
    (FixedHistoryTimeFactors.strict_sections L T hT k t x 0 (fun i=>w i+x) (fun _=>0)).mpr hp
  intro j
  have hj := hw hpp j
  have hage : targets L k p (leafIndex k (fun i=>i) j)=targets L k a (leafIndex k (fun i=>i) j) := by
    have hpAge : targets L k p (leafIndex k (fun i=>i) j)=lower L k p j := by
      rw [targets,leaf_observation L k p j]
    have haAge : targets L k a (leafIndex k (fun i=>i) j)=lower L k a j := by
      rw [targets,leaf_observation L k a j]
    rw [hpAge,haAge,FixedHistoryTimeFactors.lower_sections L T hT k t x 0 (fun i=>w i+x) (fun _=>0)]
  change normTwo haarAddCircle (fun x=>ControlledProfile.derivative P Λ u d
    ((targets L k p (leafIndex k (fun i=>i) j),x),θ))≤
    sharpConstant P d*(targets L k p (leafIndex k (fun i=>i) j))^((P.exponent-1)/4) at hj
  rw [hage] at hj
  exact hj

end SHE.BaselineSharpHistory
