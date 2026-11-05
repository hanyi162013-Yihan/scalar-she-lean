module
public import SHE.OrdinaryGradientBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OrdinaryTerminalGradientBound
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation WordRecursion OrthogonalItoChannels CutoffWordLevel
open scoped NNReal ENNReal
local instance ordinaryTerminalGradientBound_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryTerminalGradientBound_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryTerminalGradientBound_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryTerminalGradientBound_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryTerminalGradientBound_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)

theorem row_terminal_cap (p:Y)(z:ℝ≥0×Ω)(hz:(z.1:ℝ)<L.terminal p)(i:Fin n):
    ‖OrdinaryPhysicalGradient.row m (L.observations.observations p) z i‖≤
      Real.sqrt (NativeObservationCaps.cap (κ+M) (L.terminal p-(z.1:ℝ))):=by
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hp:=NativeObservationCaps.cap_nonneg (add_nonneg m.additive_pos.le hM) (sub_pos.mpr hz)
  apply (Real.le_sqrt (norm_nonneg _) hp).mpr
  have ht:(z.1:ℝ)<(L.observations.observations p i).target:=hz.trans_le (L.targets_after p i)
  have h0:=NativeObservationProcess.row_norm_sq_bound m.additive_pos
    (AdditiveHaarForcing.constantField κ m.additive_pos) ht le_rfl (L.observations.observations p i).center
  have h1:=NativeObservationProcess.row_norm_sq_bound m.lower_pos
    (m.coefficient z) ht le_rfl (L.observations.observations p i).center
  have hpow:((L.observations.observations p i).target-(z.1:ℝ))^(-(1/2:ℝ))≤
      (L.terminal p-(z.1:ℝ))^(-(1/2:ℝ)):=
    Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hz) (sub_le_sub_right (L.targets_after p i) _) (by norm_num)
  rw [OrdinaryPhysicalGradient.row,WithLp.prod_norm_sq_eq_of_L2]
  change ‖NativeObservationCovariance.row m.additive_pos (AdditiveHaarForcing.constantField κ m.additive_pos)
      (L.observations.observations p i).target (z.1:ℝ) (L.observations.observations p i).center‖^2+
    ‖NativeObservationCovariance.row m.lower_pos (m.coefficient z)
      (L.observations.observations p i).target (z.1:ℝ) (L.observations.observations p i).center‖^2≤_
  dsimp only [NativeObservationCaps.cap]
  have hfac:=mul_le_mul_of_nonneg_left hpow heatConstant_pos.le
  nlinarith [mul_nonneg m.additive_pos.le (sub_nonneg.mpr hfac),mul_nonneg hM (sub_nonneg.mpr hfac)]

/-- A true terminal-age cap remains integrable when the root heat gap
vanishes, with the actual ordinary-U additive/residual rows. -/
theorem raw_terminal_cap {C:ℝ}(hC:0≤C)
    (hgrad:∀p t z,‖fderiv ℝ (GaussianItoTest.backward (L.window p) (L.test p) t) z‖≤C)
    (z:Y×(ℝ≥0×Ω))(hz:R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<L.terminal z.1):
    ‖OrdinaryPhysicalGradient.raw m L z‖≤
      n*C*Real.sqrt (NativeObservationCaps.cap (κ+M) (L.terminal z.1-(z.2.1:ℝ))):=by
  rw [OrdinaryPhysicalGradient.raw,if_pos hz]
  calc
    _≤∑i:Fin n,‖(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
        (OrdinaryPhysicalGradient.mean m L z) (EuclideanSpace.basisFun (Fin n) ℝ i)) •
        OrdinaryPhysicalGradient.row m (L.observations.observations z.1) z.2 i‖:=norm_sum_le _ _
    _≤∑_:Fin n,C*Real.sqrt (NativeObservationCaps.cap (κ+M) (L.terminal z.1-(z.2.1:ℝ))):=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have hg:=(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
        (OrdinaryPhysicalGradient.mean m L z)).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
      rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at hg
      exact mul_le_mul (hg.trans (hgrad _ _ _)) (row_terminal_cap m L z.1 z.2 hz.2 i) (norm_nonneg _) hC
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];push_cast;ring

end SHE.OrdinaryTerminalGradientBound
