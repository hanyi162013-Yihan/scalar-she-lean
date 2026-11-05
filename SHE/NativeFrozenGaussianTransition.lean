module
public import SHE.NativeFrozenGaussianFamily
public import SHE.RandomGaussianMatrixIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeFrozenGaussianTransition
open Set MeasureTheory PredictableL2 GaussianMatrixFamily NativeFrozenGaussianRows
open GaussianMatrixGramCurve ControlledProfile OrthogonalItoChannels FiniteHaar StoppedFourier
open scoped NNReal ENNReal
local instance period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeSigma : MeasurableSpace CircleL2:=borel _
local instance nativeBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeSecond : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ]
variable (v b:ℝ≥0) (hvb:v≤b) (P:CanonicalCovariance.ProfileParameters) (Λ κ:ℝ) (hκ:0<κ) (hκP:κ<P.lower)
variable {n:ℕ}(side:Fin n→Bool) (ξ:Fin n→ℝ) (center:Fin n→HeatCircle)
variable (hΛ:0≤Λ) (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "Curve"=>NativeFrozenGaussianCurve.curve 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center

variable (H:ℝ≥0) (hbH:b≤H) (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data)
local notation "R"=>NativeFrozenGaussianRows.rows 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH
local notation "Q"=>GaussianStoppedRows.rows 𝓕 μ H v b R


variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
local notation "Y"=>SingularVectorIntegral.value 𝓕 μ H b J (0:WordRecursion.State n) Q

include hΛ hsmall in
/-- Actual original-J finite frozen observations, conditional on the
original past. Their covariance is the full shared-Haar Gram, including
all residual cross covariances; no independence of compatible residuals
is asserted or assumed. -/
theorem conditional_smooth (hb0:0<b) (hb1:(b:ℝ)≤1)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hlocal:StandardTerminalPastLocality J)
    (m:Inputs→WordRecursion.State n) (hm:Continuous m)
    {F:WordRecursion.State n→ℝ} (hF:SmoothCylinders.BoundedSmooth F)
    (A:Set Ω) (hA:MeasurableSet[𝓕 v] A):
    (∫ω in A,F (GaussianStoppedRows.terminal 𝓕 μ H v b R J (0:WordRecursion.State n) ω+m (data ω)) ∂μ)=
      ∫ω in A,GaussianConvolution.gaussianAverage ((Curve (data ω)).path (v:ℝ)).val F (m (data ω)) ∂μ:=by
  let K:Fin n→ℝ:=fun _=>NativeFrozenGaussianRows.cap P
  have hK:∀i,0≤K i:=fun _=>NativeFrozenGaussianRows.cap_nonneg P
  have hR:∀i,SingularInputBounds.Bound 𝓕 μ H b (K i) (R i):=
    NativeFrozenGaussianRows.bound 𝓕 μ H v b P Λ κ hκ hκP side ξ center data hdata hbH hb1
  have hQ:=GaussianStoppedRows.rows_bound 𝓕 μ H v b R K hK hR
  have hY:=SingularVectorIntegral.predictable_value 𝓕 μ H b J (0:WordRecursion.State n) Q
    hbH hb0 hnull B hBDG K hK hQ
  have hrep:=GaussianStoppedRows.representation 𝓕 μ H v b R J (0:WordRecursion.State n)
    hbH hb0 B hBDG K hK hR
  have hs:(fun ω=>Y (v,ω))=ᵐ[μ] fun _=>0:=by
    filter_upwards [hrep v,Lp.coeFn_zero ℝ 2 μ] with ω hy hz
    rw [hy]
    apply PiLp.ext
    intro i
    change (0:ℝ)+J.integral (StoppedItoInputs.stop 𝓕 μ H (v:ℝ) (Q i)) ω=0
    rw [GaussianStoppedRows.stop_at_past,map_zero]
    simpa only [zero_add,Pi.zero_apply] using hz
  let major:ℝ→ℝ:=fun t=>P.upper*(1+heatConstant*((b:ℝ)-t)^(-(1/2:ℝ)))
  have hmi:IntervalIntegrable major volume (v:ℝ) b:=
    CovarianceEndpoint.endpoint_majorant_integrable P.upper
  have hm0:∀t∈Ioo (v:ℝ) (b:ℝ),0≤major t:=by
    intro t ht
    dsimp [major]
    exact mul_nonneg P.upper_nonneg (add_nonneg zero_le_one (mul_nonneg heatConstant_pos.le (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _)))
  have hmb:∀p,∀t∈Ioo (v:ℝ) (b:ℝ),∀i j,|((Curve p).density t) i j|≤major t:=by
    intro p t ht i j
    exact NativeFrozenGaussianCurve.gram_bound v b P Λ κ hκ hκP side ξ center p
      (v.2.trans ht.1.le) ht.2 i j
  have hc:=NativeFrozenGaussianFamily.bracket 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center
    H hbH data hdata
  let S:=NativeFrozenGaussianFamily.family 𝓕 μ v b hvb P Λ κ hκ hκP side ξ center hΛ hsmall m hm
  have he:=RandomGaussianMatrixIto.conditional_smooth 𝓕 μ H v b J Q Y hY S rfl rfl (0,0)
    hJ hlocal (0:WordRecursion.State n)
    (SingularVectorIntegral.continuous_value 𝓕 μ H b J (0:WordRecursion.State n) Q hb0)
    (fun t _=>hrep t) hvb hbH major hmi hm0 hmb hdata.stronglyMeasurable hs hc hF A hA
  have ht:(fun ω=>Y (b,ω))=ᵐ[μ] GaussianStoppedRows.terminal 𝓕 μ H v b R J (0:WordRecursion.State n):=by
    filter_upwards [hrep b] with ω hy
    rw [hy]
    apply PiLp.ext
    intro i
    change (0:ℝ)+J.integral (StoppedItoInputs.stop 𝓕 μ H (b:ℝ) (Q i)) ω=_
    simp only [GaussianStoppedRows.rows,StoppedInputAlgebra.stop_stop,min_self,
      GaussianStoppedRows.terminal,WithLp.ofLp_toLp]
    simp
  calc
    _=∫ω in A,F (Y (b,ω)+m (data ω)) ∂μ:=by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae ht] with ω hω
      rw [hω]
    _=_:=he

end SHE.NativeFrozenGaussianTransition
