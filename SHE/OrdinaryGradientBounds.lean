module
public import SHE.OrdinaryPhysicalGradient
public import SHE.NativeObservationCaps

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OrdinaryGradientBounds
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel
open scoped NNReal ENNReal
local instance ordinaryGradientBounds_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryGradientBounds_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryGradientBounds_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryGradientBounds_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryGradientBounds_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)

theorem gradient_bound:∃C:ℝ,0≤C∧∀p t z,
    ‖fderiv ℝ (GaussianItoTest.backward (L.window p) (L.test p) t) z‖≤C:=by
  obtain ⟨C₀,_,hB₀⟩:=L.test_uniform.norm_bound
  obtain ⟨C,hC,hB⟩:=L.test_uniform.fderiv.norm_bound
  exact ⟨C,hC,fun p t z=>BackwardRegularity.gaussian_state_gradient_bound _
    ((L.test_uniform.smooth p).of_le (by simp)) (hB₀ p) (hB p) z⟩

theorem row_bound {η:ℝ}(hη:0<η)(p:Y)
    (hgap:∀i,η≤(L.observations.observations p i).target-L.terminal p)
    (z:ℝ≥0×Ω)(hz:(z.1:ℝ)≤L.terminal p)(i:Fin n):
    ‖OrdinaryPhysicalGradient.row m (L.observations.observations p) z i‖≤
      Real.sqrt (NativeObservationCaps.cap (κ+M) η):=by
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hp:=NativeObservationCaps.cap_nonneg (add_nonneg m.additive_pos.le hM) hη
  apply (Real.le_sqrt (norm_nonneg _) hp).mpr
  have ht:L.terminal p<(L.observations.observations p i).target:=by linarith [hgap i]
  have h0:=NativeObservationProcess.row_norm_sq_bound m.additive_pos
    (AdditiveHaarForcing.constantField κ m.additive_pos) ht hz (L.observations.observations p i).center
  have h1:=NativeObservationProcess.row_norm_sq_bound m.lower_pos
    (m.coefficient z) ht hz (L.observations.observations p i).center
  have hpow:((L.observations.observations p i).target-L.terminal p)^(-(1/2:ℝ))≤η^(-(1/2:ℝ)):=
    Real.rpow_le_rpow_of_nonpos hη (hgap i) (by norm_num)
  rw [OrdinaryPhysicalGradient.row,WithLp.prod_norm_sq_eq_of_L2]
  change ‖NativeObservationCovariance.row m.additive_pos (AdditiveHaarForcing.constantField κ m.additive_pos)
      (L.observations.observations p i).target (z.1:ℝ) (L.observations.observations p i).center‖^2+
    ‖NativeObservationCovariance.row m.lower_pos (m.coefficient z)
      (L.observations.observations p i).target (z.1:ℝ) (L.observations.observations p i).center‖^2≤_
  dsimp only [NativeObservationCaps.cap]
  have hfac:=mul_le_mul_of_nonneg_left hpow heatConstant_pos.le
  nlinarith [mul_nonneg m.additive_pos.le (sub_nonneg.mpr hfac),mul_nonneg hM (sub_nonneg.mpr hfac)]

theorem raw_bound {η:ℝ}(hη:0<η)
    (hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p):
    ∃B:ℝ,0≤B∧∀z,‖OrdinaryPhysicalGradient.raw m L z‖≤B:=by
  obtain ⟨C,hC,hCb⟩:=gradient_bound L
  let D:=Real.sqrt (NativeObservationCaps.cap (κ+M) η)
  refine ⟨n*C*D,by positivity,fun z=>?_⟩
  by_cases hz:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<L.terminal z.1
  · rw [OrdinaryPhysicalGradient.raw,if_pos hz]
    calc
      _≤∑i:Fin n,‖(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
          (OrdinaryPhysicalGradient.mean m L z) (EuclideanSpace.basisFun (Fin n) ℝ i)) •
          OrdinaryPhysicalGradient.row m (L.observations.observations z.1) z.2 i‖:=norm_sum_le _ _
      _≤∑_:Fin n,C*D:=by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        have hg:=(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
          (OrdinaryPhysicalGradient.mean m L z)).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
        rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at hg
        exact mul_le_mul (hg.trans (hCb _ _ _)) (row_bound m L hη z.1 (hgap z.1) z.2 hz.2.le i)
          (norm_nonneg _) hC
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];push_cast;ring
  · rw [OrdinaryPhysicalGradient.raw,if_neg hz,norm_zero]
    positivity

end SHE.OrdinaryGradientBounds
