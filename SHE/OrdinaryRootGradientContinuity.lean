module
public import SHE.OrdinaryPhysicalGradient
public import SHE.RootHeatGradientContinuity
public import SHE.NativeRowTargetContinuity
public import SHE.ObservationTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryRootGradientContinuity
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel CutoffWordHistories Filter Topology
open scoped NNReal ENNReal
local instance ordinaryRootGradientContinuity_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryRootGradientContinuity_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryRootGradientContinuity_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance ordinaryRootGradientContinuity_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryRootGradientContinuity_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryRootGradientContinuity_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryRootGradientContinuity_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)(δ:ℝ)(hδ:0<δ)(k:ℕ)
local notation "Q"=>RootHeatBounds.level L δ hδ

theorem mean_continuous (z:History Y k×(ℝ≥0×Ω))
    (hz:(z.2.1:ℝ)<(Q 0 k).terminal z.1):
    Continuous (fun ε:ℝ≥0=>OrdinaryPhysicalGradient.mean m (Q ε k) z):=by
  let Obs:=fun ε:ℝ≥0=>(Q ε k).observations.observations z.1
  have hg(ε:ℝ≥0)(i:Fin (n+k)):(z.2.1:ℝ)<(Obs ε i).target:=by
    have hh:=(Q ε k).targets_after z.1 i
    rw [RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1] at hh
    exact hz.trans_le hh
  have ho:=ObservationTargetContinuity.continuous_observe Obs (fun i=>(Obs 0 i).center)
    (RootHeatTargets.target_continuous L δ hδ k z.1)
    (fun ε i=>RootHeatTargets.center_eq L δ hδ ε 0 k z.1 i)
    (z.2.1:ℝ) hg (fun t=>m.physicalState (z.2.2,t)) (fun q=>m.physicalField (z.2.2,q))
  convert! ho using 1
  funext ε
  apply OrdinaryPhysicalGradient.mean_eq_observe
  rw [RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1]
  exact hz

theorem row_continuous (z:History Y k×(ℝ≥0×Ω))
    (hz:(z.2.1:ℝ)<(Q 0 k).terminal z.1)(i:Fin (n+k)):
    Continuous (fun ε:ℝ≥0=>OrdinaryPhysicalGradient.row m ((Q ε k).observations.observations z.1) z.2 i):=by
  let Obs:=fun ε:ℝ≥0=>(Q ε k).observations.observations z.1
  have hg(ε:ℝ≥0):(z.2.1:ℝ)<(Obs ε i).target:=by
    have hh:=(Q ε k).targets_after z.1 i
    rw [RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1] at hh
    exact hz.trans_le hh
  have hr {l W:ℝ}(hl:0<l)(f:EllipticField l W):Continuous (fun ε:ℝ≥0=>
      NativeObservationCovariance.row hl f (Obs ε i).target (z.2.1:ℝ) (Obs 0 i).center):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (NativeRowTargetContinuity.row_continuousAt_target hl f (hg ε) _).comp
      (f:=fun η:ℝ≥0=>(Obs η i).target) (x:=ε)
      (RootHeatTargets.target_continuous L δ hδ k z.1 i).continuousAt
  have hc:=(WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).comp
    ((hr m.additive_pos (AdditiveHaarForcing.constantField κ m.additive_pos)).prodMk (hr m.lower_pos (m.coefficient z.2)))
  convert! hc using 1
  funext ε
  simp only [Function.comp_def,OrdinaryPhysicalGradient.row,
    RootHeatTargets.center_eq L δ hδ ε 0 k z.1 i]
  rfl

/-- The whole actual ordinary input varies continuously through native
zero root heat age on every strict current section. -/
theorem raw_continuous (z:History Y k×(ℝ≥0×Ω)):
    Continuous (fun ε:ℝ≥0=>OrdinaryPhysicalGradient.raw m (Q ε k) z):=by
  by_cases hvq:R.base<(z.2.1:ℝ)
  · by_cases hq:(z.2.1:ℝ)<(Q 0 k).terminal z.1
    · have hMean:=mean_continuous m L δ hδ k z hq
      have hG:=RootHeatGradientContinuity.continuous_gradient L δ hδ k z.1 (z.2.1:ℝ)
      have hh:=hG.comp (continuous_id.prodMk hMean)
      have hs:=continuous_finsetSum Finset.univ (fun i _=>
        (hh.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin (n+k)) ℝ i))).smul
          (row_continuous m L δ hδ k z hq i))
      convert! hs using 1
      funext ε
      rw [OrdinaryPhysicalGradient.raw,if_pos ⟨hvq,by
        rw [RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1];exact hq⟩]
      rfl
    · have he:(fun ε:ℝ≥0=>OrdinaryPhysicalGradient.raw m (Q ε k) z)=fun _=>0:=by
        funext ε
        rw [OrdinaryPhysicalGradient.raw]
        apply if_neg
        rintro ⟨_,hh⟩
        rw [RootHeatBounds.terminal_eq L δ hδ ε 0 k z.1] at hh
        exact hq hh
      rw [he];exact continuous_const
  · have he:(fun ε:ℝ≥0=>OrdinaryPhysicalGradient.raw m (Q ε k) z)=fun _=>0:=by
      funext ε
      rw [OrdinaryPhysicalGradient.raw]
      exact if_neg (fun hh=>hvq hh.1)
    rw [he];exact continuous_const

end SHE.OrdinaryRootGradientContinuity
