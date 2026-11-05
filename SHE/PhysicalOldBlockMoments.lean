module

public import SHE.OldIntervalVariance
public import SHE.GaussianRoughBlockMoments
public import SHE.GaussianClipMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.PhysicalOldBlockMoments
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement GaussianAudit
  OldIntervalCovariance OldIntervalVariance StoppedGaussianFeatures StoppedFourier ProfileVariance
  GaussianAssignmentBlocks GaussianRoughBlocks GaussianRoughBlockMoments GaussianClipMoments
open scoped NNReal InnerProductSpace BigOperators
local instance : Fact (0<2*π):=⟨by positivity⟩

theorem physical_variance_power {V M δ β:ℝ}(hV:0≤V)(hM:0≤M)(hδ:0<δ)(hβ:0≤β)
    (hb:V≤upperConstant*M*δ^(1/2:ℝ)):
    V^(β/2)≤(upperConstant*M)^(β/2)*δ^(β/4):=by
  have hh:=rpow_le_rpow hV hb (by positivity:0≤β/2)
  rw[Real.mul_rpow (mul_nonneg upperConstant_pos.le hM) (rpow_nonneg hδ.le _),
    ←Real.rpow_mul hδ.le] at hh
  convert! hh using 1
  congr 2
  ring

/-- Actual old interval covariances supply the minimum-increment rough
gain. The selected assigned interval is arbitrary, so the best gap can
be chosen separately for each nonempty block. -/
theorem rough_block_even_moment {n r k:ℕ}(σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)(hages:∀i,σ i≤target i)
    (c:Domain→ℝ)(hc:Measurable c){M:ℝ}(hcb:∀p,0≤c p ∧ c p≤M)
    (lo hi:Fin r→ℝ)(hlo:∀j,0≤lo j)(hgap:∀j,lo j<hi j)(hstop:∀j i,σ i≤lo j ∨ hi j≤σ i)
    (choices:List (Fin r×Fin k))(hnd:(choices.map Prod.fst).Nodup)(factor:Fin k)(i:Fin r)
    (hchosen:i∈block choices factor)(leaf:Fin n)(a:ℝ→ℝ)(ha:Measurable a)
    {H β:ℝ}(hH:0≤H)(hβ:0≤β)(hholder:∀z w,|a z-a w|≤H*|z-w|^β)(mean:ℝ)(p:ℕ):
    let A:=familyCovariance σ target center c lo hi
    let L:=fun _:Fin r=>EuclideanSpace.proj (𝕜:=ℝ) leaf
    Integrable (fun y=>|blockFunction choices factor a mean L y|^(2*p))
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))) ∧
    (∫y,|blockFunction choices factor a mean L y|^(2*p) ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))≤
      gaussianAbsMoment (((2*p:ℕ):ℝ)*β)*
        ((2:ℝ)^((block choices factor).length-1)*H*(upperConstant*M)^(β/2)*(hi i-lo i)^(β/4))^(2*p):=by
  intro A L
  have hh:=block_even_moment A choices hnd factor i hchosen a ha hH hβ hholder mean L p
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hM:0≤M:=(hcb (0,0)).1.trans (hcb (0,0)).2
  have hv:=coordinate_variance_bound σ target center hσ hσ1 hages c hc hcb (hlo i) (hgap i) (hstop i) leaf
  have hv':Var[L i;multivariateGaussian 0 (A i)]^(β/2)≤
      (upperConstant*M)^(β/2)*(hi i-lo i)^(β/4):=
    physical_variance_power (variance_nonneg _ _) hM (sub_pos.mpr (hgap i)) hβ hv
  have hs:(2:ℝ)^((block choices factor).length-1)*H*Var[L i;multivariateGaussian 0 (A i)]^(β/2)≤
      (2:ℝ)^((block choices factor).length-1)*H*(upperConstant*M)^(β/2)*(hi i-lo i)^(β/4):=by
    convert! mul_le_mul_of_nonneg_left hv' (show 0≤(2:ℝ)^((block choices factor).length-1)*H by positivity) using 1
    ring
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
    positivity[variance_nonneg (L i) (multivariateGaussian (0:State n) (A i))]:0≤
    (2:ℝ)^((block choices factor).length-1)*H*Var[L i;multivariateGaussian 0 (A i)]^(β/2)) hs (2*p))
    (gaussianAbsMoment_nonneg _)

/-- Every actual old root clip retains its original physical interval
gap, even when it is correlated with its own insertion score. -/
theorem root_clip_even_moment {n r:ℕ}(σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)(hages:∀i,σ i≤target i)
    (c:Domain→ℝ)(hc:Measurable c){M:ℝ}(hcb:∀p,0≤c p ∧ c p≤M)
    (lo hi:Fin r→ℝ)(hlo:∀j,0≤lo j)(hgap:∀j,lo j<hi j)(hstop:∀j i,σ i≤lo j ∨ hi j≤σ i)
    (i:Fin r)(leaf:Fin n){ν:ℝ}(hν:0≤ν)(p:ℕ):
    let A:=familyCovariance σ target center c lo hi
    Integrable (fun y:Fin r→State n=>|clip ν (y i leaf)|^(2*p))
      (Measure.pi (fun j=>multivariateGaussian 0 (A j))) ∧
    (∫y:Fin r→State n,|clip ν (y i leaf)|^(2*p) ∂Measure.pi (fun j=>multivariateGaussian 0 (A j)))≤
      clipMomentConstant p*(min 1 (ν*sqrt (upperConstant*M)*(hi i-lo i)^(1/4:ℝ)))^(2*p):=by
  intro A
  let L:=fun _:Fin r=>EuclideanSpace.proj (𝕜:=ℝ) leaf
  have hLaw:=selected_projection_hasLaw A L i
  have hh:=clip_even_moment (Measure.pi (fun j=>multivariateGaussian 0 (A j)))
    (fun y:Fin r→State n=>L i (y i)) (by fun_prop) hLaw hν p
  simp only[Real.coe_toNNReal _ (variance_nonneg (L i) (multivariateGaussian (0:State n) (A i)))] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hM:0≤M:=(hcb (0,0)).1.trans (hcb (0,0)).2
  have hv:=coordinate_variance_bound σ target center hσ hσ1 hages c hc hcb (hlo i) (hgap i) (hstop i) leaf
  have hv':sqrt (Var[L i;multivariateGaussian 0 (A i)])≤sqrt (upperConstant*M)*(hi i-lo i)^(1/4:ℝ):=by
    have ht:=physical_variance_power (variance_nonneg (L i) (multivariateGaussian (0:State n) (A i))) hM
      (sub_pos.mpr (hgap i)) (by norm_num:0≤(1:ℝ)) hv
    simpa only[one_div,Real.sqrt_eq_rpow] using ht
  have hs:min 1 (ν*sqrt (Var[L i;multivariateGaussian 0 (A i)]))≤
      min 1 (ν*sqrt (upperConstant*M)*(hi i-lo i)^(1/4:ℝ)):=by
    apply min_le_min_left
    convert! mul_le_mul_of_nonneg_left hv' hν using 1
    ring
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_min (by norm_num)
    (mul_nonneg hν (sqrt_nonneg _))) hs (2*p)) (clipMomentConstant_nonneg p)

end SHE.PhysicalOldBlockMoments
