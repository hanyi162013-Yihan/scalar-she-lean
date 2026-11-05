module

public import SHE.StoppedDefectMeanEnergy
public import SHE.NativeObservationColumnMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace SHE.NativeClippedHaarDirection
open MeasureTheory Set Real AddCircle FiniteHaar StoppedFourier StoppedGaussianScore
  StoppedDefectMeanEnergy StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  RealHeatCovarianceMean PhysicalProfile
local instance nativeClippedHaarDirection_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeClippedHaarDirection_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

def column {n:ℕ}{m M:ℝ}(hm:0<m)(c d:EllipticField m M)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)(j:HaarNode):GaussianIncrement.State n:=
  WithLp.toLp 2 (fun i=>(1-exp (-Λ*(σ i-u)))*
    (NativeObservationCovariance.row hm c (target i) u (nativeCenter a i) j-
      NativeObservationCovariance.row hm d (target i) u (nativeCenter a i) j))

/-- The clipped canonical score direction is the literal SAME-Haar
analysis-row difference of the two actual coefficient factors. Original
stops only enter their own damping weight, while targets enter heat. -/
theorem column_eq_meanDirection {n:ℕ}{m M:ℝ}(hm:0<m)(c d:EllipticField m M)
    (σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀i,u<σ i)(j:HaarNode):
    column hm c d σ target a u Λ j=
      meanDirection (clippedSynthesis σ target a u Λ t hage act)
        (globalSignedColumn j c.1 d.1):=by
  apply PiLp.ext
  intro i
  change (1-exp (-Λ*(σ i-u)))*
    (NativeObservationCovariance.row hm c (target i) u (nativeCenter a i) j-
      NativeObservationCovariance.row hm d (target i) u (nativeCenter a i) j)=_
  rw [meanDirection_apply,clippedSynthesis_basis,inner_smul_left]
  simp only [map_sub,map_one,Complex.conj_ofReal,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  congr 1
  have hi:=CircleNormalization.push.inner_map_map (unitHeatKernel (t i) (a i))
    (globalSignedColumn j c.1 d.1)
  rw [HeatMarkov.push_unitHeatKernel,←hage i] at hi
  rw [←hi]
  have hagei:u<target i:=by
    have hh:0<target i-u:=by
      rw [hage i]
      exact mul_pos (by positivity) (ht i)
    linarith
  rw [NativeObservationColumnMean.row hm c hagei,NativeObservationColumnMean.row hm d hagei,
    physicalHeatMean_eq (sub_pos.mpr hagei),physicalHeatMean_eq (sub_pos.mpr hagei)]
  simp only [globalSignedColumn,map_sub,inner_sub_right,Complex.sub_re,nativeCenter]

end SHE.NativeClippedHaarDirection
