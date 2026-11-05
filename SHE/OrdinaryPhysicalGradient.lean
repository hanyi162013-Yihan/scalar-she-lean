module
public import SHE.OrdinaryUncutNoise
public import SHE.NativePhysicalRowFields
public import SHE.PredictableClock
public import SHE.MeasurableDerivatives

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.OrdinaryPhysicalGradient
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
  NativeHeatObservation NativeObservationNaturality WordRecursion OrthogonalItoChannels CutoffWordLevel
open scoped NNReal ENNReal
local instance ordinaryPhysicalGradient_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryPhysicalGradient_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryPhysicalGradient_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance ordinaryPhysicalGradient_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance ordinaryPhysicalGradient_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance ordinaryPhysicalGradient_realSigma:MeasurableSpace RealL2:=borel _
local instance ordinaryPhysicalGradient_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance ordinaryPhysicalGradient_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance ordinaryPhysicalGradient_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance ordinaryPhysicalGradient_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance ordinaryPhysicalGradient_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω Y:Type}[MeasurableSpace Ω][MeasurableSpace Y]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)

def mean(z:Y×(ℝ≥0×Ω)):WordRecursion.State n:=WithLp.toLp 2 (fun i=>
  PhysicalProfile.physicalHeatMean (embed (m.state z.2))
    ((L.observations.observations z.1 i).target-(z.2.1:ℝ),(L.observations.observations z.1 i).center))

def row (Z:Fin n→Observation)(z:ℝ≥0×Ω)(i:Fin n):Both RealHaarInput:=WithLp.toLp 2
  (NativeObservationCovariance.row m.additive_pos (AdditiveHaarForcing.constantField κ m.additive_pos)
      (Z i).target (z.1:ℝ) (Z i).center,
    NativeObservationCovariance.row m.lower_pos (m.coefficient z) (Z i).target (z.1:ℝ) (Z i).center)

/-- Literal ordinary-U gradient with its own rough-coefficient Haar
rows. No joint-current or reference-θ process is substituted. -/
def raw(z:Y×(ℝ≥0×Ω)):Both RealHaarInput:=
  if R.base<(z.2.1:ℝ)∧(z.2.1:ℝ)<L.terminal z.1 then
    ∑i:Fin n,(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
      (mean m L z) (EuclideanSpace.basisFun (Fin n) ℝ i)) • row m (L.observations.observations z.1) z.2 i
  else 0

theorem mean_predictable:
    @Measurable (Y×(ℝ≥0×Ω)) (WordRecursion.State n)
      ((inferInstance:MeasurableSpace Y).prod 𝓕.predictable) inferInstance (mean m L):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hU:=embed.continuous.measurable.comp m.state_predictable.measurable
  have hq:Measurable (fun z:Y×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:=(L.observations.target_measurable i).comp (measurable_fst:Measurable (Prod.fst:Y×(ℝ≥0×Ω)→_))
  have hx:=(L.observations.center_measurable i).comp (measurable_fst:Measurable (Prod.fst:Y×(ℝ≥0×Ω)→_))
  exact PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hU.comp measurable_snd).prodMk ((hT.sub hq).prodMk hx))

theorem raw_predictable:
    @Measurable (Y×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace Y).prod 𝓕.predictable) inferInstance (raw m L):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hq:Measurable (fun z:Y×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  have hd:=MeasurableDerivatives.fderiv_measurable (CutoffWordAnalytic.backward_measurable L)
    (fun q:Y×ℝ=>((CutoffWordAnalytic.backward_uniform L).smooth q).differentiable (by simp))
  have hmap:Measurable (fun z:Y×(ℝ≥0×Ω)=>((z.1,(z.2.1:ℝ)),mean m L z)):=
    (measurable_fst.prodMk hq).prodMk (mean_predictable m L)
  have hgrad:=hd.comp hmap
  have hrow(i:Fin n):Measurable (fun z:Y×(ℝ≥0×Ω)=>row m (L.observations.observations z.1) z.2 i):=by
    have hT:=(L.observations.target_measurable i).comp (measurable_fst:Measurable (Prod.fst:Y×(ℝ≥0×Ω)→_))
    have hx:=(L.observations.center_measurable i).comp (measurable_fst:Measurable (Prod.fst:Y×(ℝ≥0×Ω)→_))
    have h0:=NativePhysicalRowFields.row_measurable_comp m.additive_pos
      (measurable_const (a:=AdditiveHaarForcing.constantField κ m.additive_pos)) hT hq hx
    have h1:=NativePhysicalRowFields.row_measurable_comp m.lower_pos
      (m.coefficient_predictable.measurable.comp measurable_snd) hT hq hx
    exact (WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp (h0.prodMk h1)
  have hs:Measurable (fun z:Y×(ℝ≥0×Ω)=>∑i:Fin n,
      (fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
        (mean m L z) (EuclideanSpace.basisFun (Fin n) ℝ i)) • row m (L.observations.observations z.1) z.2 i):=
    Finset.measurable_fun_sum _ (fun i _=>
      ((ContinuousLinearMap.measurable_apply (EuclideanSpace.basisFun (Fin n) ℝ i)).comp hgrad).smul (hrow i))
  exact hs.ite ((measurableSet_lt measurable_const hq).inter
    (measurableSet_lt hq (L.terminal_measurable.comp measurable_fst))) measurable_const

theorem mean_eq_observe (p:Y)(z:ℝ≥0×Ω)(hz:(z.1:ℝ)<L.terminal p):
    mean m L (p,z)=observe (fun t=>m.physicalState (z.2,t))
      (fun q=>m.physicalField (z.2,q)) (L.observations.observations p) (z.1:ℝ):=by
  apply PiLp.ext
  intro i
  have hi:(z.1:ℝ)<(L.observations.observations p i).target:=hz.trans_le (L.targets_after p i)
  simp only [mean,observe,WithLp.ofLp_toLp,if_pos hi,TwoChannelCutoffModel.Model.physicalState,Real.toNNReal_coe]

end SHE.OrdinaryPhysicalGradient
