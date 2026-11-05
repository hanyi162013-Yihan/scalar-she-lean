module

public import SHE.NativeReserveRowEnvelope
public import SHE.NativeHeatRoot
public import SHE.StoppedScoreTranslation
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section
namespace SHE.NativeReserveTranslatedEnvelope
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  PhysicalScoreChain StoppedGaussianFeatures MeasurableGaussianScores
open scoped BigOperators
local instance nativeReserveTranslatedEnvelope_period:Fact (0<2*π):=⟨by positivity⟩
variable {n:ℕ}

def translate (Z:Fin n→Observation) (x:HeatCircle):Fin n→Observation:=
  fun i=>⟨(Z i).stop,(Z i).target,(Z i).center+x⟩

theorem covariance_translate (P:CanonicalCovariance.ProfileParameters) (Z:Fin n→Observation)
    (x:HeatCircle) (q:ℝ):
    NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>(translate Z x i).center) q=
    NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>(Z i).center) q:=by
  unfold NativeFirstScoreReserve.covariance
  exact StoppedScoreLeverage.stoppedCovariance_translate _ _ _ x (fun _=>NativeFirstScoreReserve.floor P) q

theorem row_translate (Z:Fin n→Observation) (r:ℝ) (y x:HeatCircle):
    heatRow (translate Z x) r y=heatRow Z r (y-x):=by
  apply PiLp.ext
  intro i
  change (ProfileVariance.heatPhysical ((Z i).target-r) ((Z i).center+x) y).re=
    (ProfileVariance.heatPhysical ((Z i).target-r) (Z i).center (y-x)).re
  have hh:=StoppedScoreLeverage.heatPhysical_translate ((Z i).target-r) (Z i).center (y-x) x
  simpa only [sub_add_cancel] using congrArg Complex.re hh

/-- One fixed-frame native score event is transported through the TRUE
joint input/output Haar variables. No adaptive center is substituted into
a fixed-frame AE envelope. Every original parent remains in the sum. -/
theorem joint_parent_envelope (n:ℕ):
    ∃H C:ℝ,0<H ∧ 0<C ∧
      ∀(P:CanonicalCovariance.ProfileParameters) (Z:Fin n→Observation)
      (hages:∀i,(Z i).stop≤(Z i).target) {q r hi:ℝ} (hq:0≤q) (hqr:q≤r) (hrhi:r<hi)
      (hstop:∀i,hi≤(Z i).stop) (hsmall:∀i,(Z i).target-r≤H),
      ∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
        let Zx:=translate Z yx.2
        let R:=NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target)
          (fun i=>(Zx i).center) q
        heatRow Zx r yx.1∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range ∧
          sqrt (scoreVariance R (heatRow Zx r yx.1))≤
            sqrt (C/((P.lower/8)*(hi-r)))*NativeHeatSpan.sqrtKernelConstant*
              ∑i,((Z i).target-r)^(1/4:ℝ)*
                ‖NativeHeatSpan.kernel (8*((Z i).target-r)) (by have := hages i; have := hstop i; linarith)
                  ((Z i).center+yx.2) yx.1‖:=by
  obtain ⟨H,C,hH,hC,hbound⟩:=NativeReserveRowEnvelope.sqrt_heat_envelope n
  refine ⟨H,C,hH,hC,?_⟩
  intro P Z hages q r hi hq hqr hrhi hstop hsmall
  have hh:=hbound P Z hages hq hqr hrhi hstop hsmall
  have hp:∀ᵐyx:HeatCircle×HeatCircle∂haarAddCircle.prod haarAddCircle,
      (heatRow Z r (yx.1-yx.2)∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q)).range) ∧
      sqrt (scoreVariance (NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q)
        (heatRow Z r (yx.1-yx.2)))≤sqrt (C/((P.lower/8)*(hi-r)))*
          ∑i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center (yx.1-yx.2)‖:=by
    simpa only [sub_eq_add_neg,add_comm] using
      (quasiMeasurePreserving_neg_add_swap (μ:=haarAddCircle) (ν:=haarAddCircle)).ae hh
  filter_upwards [hp] with yx hyx
  dsimp only
  rw [covariance_translate,row_translate]
  refine ⟨hyx.1,hyx.2.trans ?_⟩
  have hcoef:0≤sqrt (C/((P.lower/8)*(hi-r))):=sqrt_nonneg _
  have hsum:(∑i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center (yx.1-yx.2)‖)≤
      NativeHeatSpan.sqrtKernelConstant*∑i,((Z i).target-r)^(1/4:ℝ)*
        ‖NativeHeatSpan.kernel (8*((Z i).target-r)) (by have := hages i; have := hstop i; linarith)
          ((Z i).center+yx.2) yx.1‖:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi:0<(Z i).target-r:=by linarith [hages i,hstop i]
    have hh:=NativeHeatSpan.sqrt_kernel_four_eight hi (Z i).center (yx.1-yx.2)
    have ht:=StoppedScoreLeverage.heatPhysical_translate (8*((Z i).target-r)) (Z i).center (yx.1-yx.2) yx.2
    rw [sub_add_cancel] at ht
    rw [←ht] at hh
    simpa only [NativeHeatSpan.kernel_eq_physical,mul_assoc] using hh
  exact (mul_le_mul_of_nonneg_left hsum hcoef).trans_eq (by ring)

end SHE.NativeReserveTranslatedEnvelope
