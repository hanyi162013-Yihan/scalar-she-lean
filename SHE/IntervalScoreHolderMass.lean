module
public import SHE.ScoreMixedMass
public import SHE.StoppedRowSquareMass
public import SHE.IntervalScoreMass

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.IntervalScoreHolderMass
open Set MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures
  StoppedFourier WordRecursion ProfileVariance OldIntervalCovariance MeasurableGaussianScores
open scoped BigOperators
local instance intervalScoreHolderMass_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n:ℕ}

def constant (n:ℕ)(ell β:ℝ):ℝ:=
  (((n:ℝ)+1)/ell)^(1-β/2)*(1+heatConstant)^(β/2)

theorem power_identity {ell δ β:ℝ}(hell:0<ell)(hδ:0<δ)(n:ℕ):
    (((n:ℝ)+1)/(ell*δ))^(1-β/2)*
      ((1+heatConstant)*δ^(-(1/2:ℝ)))^(β/2)=constant n ell β*δ^(β/4-1):=by
  have hC:0≤1+heatConstant:=by linarith [heatConstant_pos]
  have ha:((n:ℝ)+1)/(ell*δ)=(((n:ℝ)+1)/ell)*δ^(-1:ℝ):=by
    rw [Real.rpow_neg_one]
    field_simp
  rw [ha,Real.mul_rpow (div_nonneg (by positivity) hell.le) (Real.rpow_nonneg hδ.le _),
    Real.mul_rpow hC (Real.rpow_nonneg hδ.le _),←Real.rpow_mul hδ.le,←Real.rpow_mul hδ.le]
  calc
    _=constant n ell β*(δ^((-1)*(1-β/2))*δ^((-(1/2:ℝ))*(β/2))):=by unfold constant;ring
    _=constant n ell β*δ^(β/4-1):=by
      rw [←Real.rpow_add hδ]
      congr 2
      ring

/-- The fresh physical score/row mixed mass gains exactly β/4 in the
fresh time gap. It is proved from the true finite covariance and native
heat-square masses, with no spatial-envelope or conditioning premise. -/
theorem mixed_bound (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hages:∀i,σ i≤target i)(c:Domain→ℝ)(hc:Measurable c)
    {lo hi ell M β:ℝ}(hlo:0≤lo)(hgap:lo<hi)(hgap1:hi-lo≤1)
    (hstop:∀i,σ i≤lo ∨ hi≤σ i)(hell:0<ell)(hb:∀p,ell≤c p ∧ c p≤M)
    (hβ:0≤β)(hβ2:β≤2)
    (T:MeasurableGeneralizedInverse.Mat n)(hT:T.PosSemidef)
    (hAT:(T-stoppedCovariance σ target center (intervalProfile c lo hi) 0).PosSemidef)(i:Fin n):
    Integrable (fun x:HeatCircle=>scoreVariance T (stoppedRow σ target center (lo,x))^(1-β/2)*
      |stoppedRow σ target center (lo,x) i|^β) haarAddCircle ∧
    (∫x:HeatCircle,scoreVariance T (stoppedRow σ target center (lo,x))^(1-β/2)*
      |stoppedRow σ target center (lo,x) i|^β ∂haarAddCircle)≤constant n ell β*(hi-lo)^(β/4-1):=by
  let A:=stoppedCovariance σ target center (intervalProfile c lo hi) 0
  have hA:A.PosSemidef:=OldIntervalCovariance.covariance_posSemidef σ target center hages c hc
    (fun p=>⟨hell.le.trans (hb p).1,(hb p).2⟩) lo hi
  have hr:Measurable (fun x:HeatCircle=>stoppedRow σ target center (lo,x)):=
    (stoppedRow_measurable σ target center).comp (measurable_const.prodMk measurable_id)
  have hrow:=OldIntervalCovariance.endpoint_row_mem_range_unrestricted σ target center hages hlo hgap hstop c hc hell hb
  have hmass:=IntervalScoreMass.score_mass_bound σ target center hages c hc hlo hgap hstop hell hb
  have hsq:=StoppedRowSquareMass.coordinate_bound σ target center hages hgap hgap1 hstop i
  have hden:0<ell*(hi-lo):=mul_pos hell (sub_pos.mpr hgap)
  have ha:0<((n:ℝ)+1)/(ell*(hi-lo)):=div_pos (by positivity) hden
  have hB:0<(1+heatConstant)*(hi-lo)^(-(1/2:ℝ)):=mul_pos (by linarith [heatConstant_pos])
    (Real.rpow_pos_of_pos (sub_pos.mpr hgap) _)
  have hcap:(∫x:HeatCircle,scoreVariance A (stoppedRow σ target center (lo,x)) ∂haarAddCircle)≤
      ((n:ℝ)+1)/(ell*(hi-lo)):=hmass.2.trans (div_le_div_of_nonneg_right (by linarith) hden.le)
  obtain ⟨hi,hbnd⟩:=ScoreMixedMass.bound haarAddCircle hA hT hAT _ hr hrow hmass.1 i hsq.1
    ha hB hβ hβ2 hcap hsq.2
  rw [power_identity hell (sub_pos.mpr hgap) n] at hbnd
  exact ⟨hi,hbnd⟩

end SHE.IntervalScoreHolderMass
