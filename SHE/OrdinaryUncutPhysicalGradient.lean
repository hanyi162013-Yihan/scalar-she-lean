module
public import SHE.OrdinaryGradientScaling
public import SHE.UncutWordEvaluation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OrdinaryUncutPhysicalGradient
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  WordRecursion OrthogonalItoChannels CutoffWordLevel CutoffWordHistories CutoffCarriers Classical
open scoped NNReal ENNReal
local instance ordinaryUncutPhysicalGradient_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryUncutPhysicalGradient_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryUncutPhysicalGradient_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryUncutPhysicalGradient_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)(k:ℕ)
local notation "NL"=>UncutWordEvaluation.normalizedLevel L k
local notation "W"=>UncutSmoothWords.weight L k

/-- Full ordinary-U gradient: the genuine original heat-history
weight multiplies the actual normalized Gaussian derivative row. -/
def raw(z:History Y k×(ℝ≥0×Ω)):Both RealHaarInput:=W z.1 • OrdinaryPhysicalGradient.raw m NL z

theorem raw_predictable:
    @Measurable (History Y k×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace (History Y k)).prod 𝓕.predictable) inferInstance (raw m L k):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).smul
    (OrdinaryPhysicalGradient.raw_predictable m NL)

theorem cutoff_eq (δ:ℝ)(hδ:0<δ)(z:History Y k×(ℝ≥0×Ω)):
    OrdinaryPhysicalGradient.raw m (RecursiveHeatBounds.level L δ hδ 0 k) z=
      if CutoffUncutComparison.Active L δ k z.1 then raw m L k z else 0:=by
  let a:=CutoffUncutComparison.Active L δ k z.1
  let w:ℝ:=if a then W z.1 else 0
  have ht:(RecursiveHeatBounds.level L δ hδ 0 k).test z.1=w • (NL).test z.1:=by
    rw [CutoffUncutComparison.test_eq_active L hδ k z.1]
    by_cases ha:a
    · dsimp only [a] at ha
      simp only [w,a,ha,ite_true]
      rw [UncutSmoothWords.test_eq_weight_normalized]
      rfl
    · dsimp only [a] at ha
      simp only [w,a,ha,ite_false,zero_smul]
  have hh:=OrdinaryGradientScaling.raw_smul m (RecursiveHeatBounds.level L δ hδ 0 k) NL w z.1
    (CutoffCarriers.observations_eq L hδ zero_lt_one k z.1)
    (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1) ht z.2
  rw [hh]
  by_cases ha:a
  · dsimp only [a] at ha
    simp only [w,a,ha,ite_true]
    rfl
  · dsimp only [a] at ha
    simp only [w,a,ha,ite_false,zero_smul]

theorem eventually_eq (z:History Y k×(ℝ≥0×Ω)):
    ∃η:ℝ,0<η∧∀δ hδ,δ<η→OrdinaryPhysicalGradient.raw m (RecursiveHeatBounds.level L δ hδ 0 k) z=raw m L k z:=by
  obtain ⟨η,hη,heq⟩:=CutoffUncutComparison.eventually_test_eq L k z.1
  refine ⟨η,hη,fun δ hδ hd=>?_⟩
  exact OrdinaryGradientScaling.raw_smul m (RecursiveHeatBounds.level L δ hδ 0 k) NL (W z.1) z.1
    (CutoffCarriers.observations_eq L hδ zero_lt_one k z.1)
    (CutoffCarriers.terminal_eq L hδ zero_lt_one k z.1)
    (by rw [heq δ hδ hd,UncutSmoothWords.test_eq_weight_normalized];rfl) z.2

end SHE.OrdinaryUncutPhysicalGradient
