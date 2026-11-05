module
public import SHE.MovingPhysicalGammaKernel
public import SHE.StoppedHeatMajorantEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MovingPhysicalGammaCap
open Set MeasureTheory FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance movingPhysicalGammaCap_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingPhysicalGammaCap_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingPhysicalGammaCap_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingPhysicalGammaCap_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingPhysicalGammaCap_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingPhysicalGammaCap_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingPhysicalGammaCap_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingPhysicalGammaCap_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω](past terminal:ℝ→ℝ≥0)
variable {κ m U:ℝ}(hκ:0<κ)(hm:0<m)(hU:0≤U)
variable (g:Fin 6→MovingPhysicalGammaKernel.Domain Ω→ℂ)(B:ℝ)(hB:0≤B)
variable (hg:∀i z,‖g i z‖≤B)
variable (c0 c1 r0 r1:ℝ×(ℝ≥0×Ω)→EllipticField m U)(d:ℝ×(ℝ≥0×Ω)→ℝ)
variable (hdb:∀z,0≤d z∧d z≤1)
local notation "Raw"=>MovingPhysicalGammaKernel.raw past terminal hκ hm g c0 c1 r0 r1 d

def coefficient (B κ U:ℝ):ℝ:=16*B^2*(κ+U)*(1+heatConstant)
def constant (B κ U:ℝ)(H:ℝ≥0):ℝ:=coefficient B κ U*(2*Real.sqrt H)

include hU hB hg hdb in
theorem raw_cap (H:ℝ≥0)(hbH:∀r,terminal r≤H)(hH:(H:ℝ)≤1)(r:ℝ)(p:ℝ≥0×Ω)(x:HeatCircle):
    ENNReal.ofReal (‖Raw ((r,p),x)‖^2)≤ENNReal.ofReal (coefficient B κ U)*
      (Iio (terminal r)).indicator
        (fun t:ℝ≥0=>ENNReal.ofReal (((terminal r:ℝ)-(t:ℝ))^(-(1/2:ℝ)))) p.1:=by
  let C:ℝ:=16*B^2*(κ+U)
  have hC:0≤C:=by dsimp only [C];positivity
  have hK:0≤coefficient B κ U:=mul_nonneg hC (by linarith [heatConstant_pos])
  by_cases hp:p∈NativeGammaClock.window (past r) (terminal r)
  · have ht:p.1<terminal r:=hp.2
    have hh:=NativeJointPhysicalGammaInput.raw_majorized (past r) (terminal r) hκ hm B hB
      (fun i p=>g i ((r,p.1),p.2)) (fun i p x=>hg i ((r,p),x))
      (fun p=>c0 (r,p)) (fun p=>c1 (r,p)) (fun p=>r0 (r,p)) (fun p=>r1 (r,p))
      (fun p=>d (r,p)) (fun p=>hdb (r,p)) p x
    change ‖Raw ((r,p),x)‖^2≤_ at hh
    have ha:0<(terminal r:ℝ)-(p.1:ℝ):=sub_pos.mpr (by exact_mod_cast ht)
    have ha1:(terminal r:ℝ)-(p.1:ℝ)≤1:=by
      have hb':(terminal r:ℝ)≤H:=by exact_mod_cast hbH r
      linarith [p.1.coe_nonneg]
    have hpow:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by norm_num:-(1/2:ℝ)≤0)
    rw [NativePhysicalGammaInput.majorant,Set.indicator_of_mem hp,
      show NativeGammaClock.age (past r) (terminal r) p=(terminal r:ℝ)-(p.1:ℝ) from if_pos hp] at hh
    rw [Set.indicator_of_mem (show p.1∈Iio (terminal r) from ht),←ENNReal.ofReal_mul hK]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [coefficient,C] at *
    nlinarith [heatConstant_pos,Real.rpow_nonneg ha.le (-(1/2:ℝ))]
  · have hz:Raw ((r,p),x)=0:=by
      simp only [MovingPhysicalGammaKernel.raw,MovingPhysicalGammaKernel.paired,
        NativePhysicalGammaKernel.raw,if_neg hp,smul_zero,add_zero]
    rw [hz,norm_zero,zero_pow (by norm_num:(2:ℕ)≠0),ENNReal.ofReal_zero]
    exact bot_le

variable (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hbH:∀r,terminal r≤H)(hH:(H:ℝ)≤1)
include hU hB hg hdb hbH hH in
/-- Genuine uniform original full-H square energy of the moving convex
physical Gamma rows. All dependence between multipliers and coefficients
is retained, and the future endpoint singularity is actually integrated. -/
theorem energy_bound (r:ℝ)(x:HeatCircle):
    (∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((r,(t,ω)),x)‖^2) ∂μ ∂timeMeasure H)≤
      ENNReal.ofReal (constant B κ U H):=by
  have he:=StoppedHeatMajorantEnergy.bound μ H (terminal r) (hbH r) (coefficient B κ U)
    (fun t ω=>ENNReal.ofReal (‖Raw ((r,(t,ω)),x)‖^2))
    (fun t ω=>raw_cap past terminal hκ hm hU g B hB hg c0 c1 r0 r1 d hdb H hbH hH r (t,ω) x)
  have hc:=heatConstant_pos
  exact he.trans_eq (by rw [←ENNReal.ofReal_mul (by dsimp only [coefficient];positivity)];rfl)
end SHE.MovingPhysicalGammaCap
