module
public import SHE.NativeFrozenGaussianLaw
public import SHE.NativeFrozenAdditiveCovariance
public import SHE.GaussianMixtureBand
public import SHE.RandomGaussianMatrixIto
public import SHE.GaussianStandardRealization

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeFrozenBandCovariance
open Set MeasureTheory ProbabilityTheory PredictableL2 GaussianMatrixFamily NativeFrozenGaussianRows
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
def sides:Fin 6→Bool:=![false,false,true,true,true,true]
def parameters (θ η:ℝ):Fin 6→ℝ:=![0,0,θ,θ,η,η]
def centers (x y:HeatCircle):Fin 6→HeatCircle:=![x,y,x,y,x,y]
variable (θ η:ℝ) (x y:HeatCircle)
variable (hΛ:0≤Λ) (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "Curve"=>NativeFrozenGaussianCurve.curve 𝓕 μ v b hvb P Λ κ hκ hκP sides (parameters θ η) (centers x y)

variable (H:ℝ≥0) (hbH:b≤H) (data:Ω→Inputs) (hdata:Measurable[𝓕 v] data)
local notation "R"=>NativeFrozenGaussianRows.rows 𝓕 μ H v b P Λ κ hκ hκP sides (parameters θ η) (centers x y) data hdata hbH
local notation "Q"=>GaussianStoppedRows.rows 𝓕 μ H v b R


variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
local notation "Y"=>SingularVectorIntegral.value 𝓕 μ H b J (0:WordRecursion.State 6) Q



local notation "C" p=>(Curve p).path (v:ℝ)
local notation "Output" m=>NativeFrozenGaussianLaw.terminal 𝓕 μ v b P Λ κ hκ hκP sides
  (parameters θ η) (centers x y) H hbH data hdata J m

include hΛ hsmall hvb in
/-- Actual original-noise compatible frozen observations satisfy the
sharp two-point polynomial Gaussian-band bound. Both random displacement
minima remain inside the original expectation. -/
theorem bound (hb0:0<b) (hb1:(b:ℝ)≤1)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J) (hlocal:StandardTerminalPastLocality J)
    (m:Inputs→WordRecursion.State 6) (hm:Continuous m)
    (hvb':v<b) (hsmalltime:(b:ℝ)-(v:ℝ)≤NativeTwoPointCovariance.horizon) (hxy:x≠y)
    {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){M K β:ℝ}
    (hM:∀z,|a z|≤M)(hK:0≤K)(hβ:0≤β)(hβ1:β≤1)
    (hh:∀z w,|a z-a w|≤K*|z-w|^β) (j:ℕ):
    let σ:ℝ≥0:=(κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128).toNNReal
    |∫ω,GaussianSeparatedBand.pair a j ((Output m) ω) ∂μ|≤
      ((2*K*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
        ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2*
      ∫ω,GaussianSeparatedBand.amplitude j ((Output m) ω) ∂μ:=by
  let σ:ℝ≥0:=(κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128).toNNReal
  have hs0:0<(b:ℝ)-(v:ℝ):=sub_pos.mpr (by exact_mod_cast hvb')
  have hσreal:0<κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128:=by
    apply div_pos (mul_pos hκ (lt_min (dist_pos.mpr hxy) (Real.sqrt_pos.mpr hs0))) (by norm_num)
  have hσ:0<σ:=Real.toNNReal_pos.mpr hσreal
  have hCov:Continuous (fun p:Inputs=>C p):=
    NativeFrozenGaussianCurve.covariance_parameter_continuous 𝓕 μ v b hvb P Λ κ hκ hκP sides
      (parameters θ η) (centers x y) hΛ hsmall v
  have hsideA:∀i:Fin 2,sides (GaussianSeparatedBand.additive i)=false:=by
    intro i;fin_cases i <;> rfl
  have hsideR:∀i:Fin 4,sides (GaussianSeparatedBand.residual i)=true:=by
    intro i;fin_cases i <;> rfl
  have hc:∀p:Inputs,∀i:Fin 4,∀l:Fin 2,(C p).val (GaussianSeparatedBand.residual i) (GaussianSeparatedBand.additive l)=0:=by
    intro p i l
    have hz:=NativeFrozenGaussianBlocks.cross_zero 𝓕 μ v b hvb P Λ κ hκ hκP sides
      (parameters θ η) (centers x y) p _ _ (hsideA l) (hsideR i)
    have he: (C p).val (GaussianSeparatedBand.residual i) (GaussianSeparatedBand.additive l)=
        (C p).val (GaussianSeparatedBand.additive l) (GaussianSeparatedBand.residual i):=by
      simpa only [star_trivial] using (C p).property.isHermitian.apply (GaussianSeparatedBand.additive l) (GaussianSeparatedBand.residual i)
    exact he.trans hz
  have hr:∀p:Inputs,((C p).val.submatrix GaussianSeparatedBand.additive GaussianSeparatedBand.additive-
      GaussianTwoPointReserve.covariance σ).PosSemidef:=by
    intro p
    rw [NativeFrozenAdditiveCovariance.covariance 𝓕 μ v b hvb P Λ κ hκ hκP sides
      (parameters θ η) (centers x y) p GaussianSeparatedBand.additive hsideA]
    have hx:centers x y (GaussianSeparatedBand.additive 0)=x:=rfl
    have hy:centers x y (GaussianSeparatedBand.additive 1)=y:=rfl
    rw [hx,hy]
    simpa only [GaussianTwoPointReserve.covariance,σ,Real.coe_toNNReal _ hσreal.le]
      using NativeTwoPointCovariance.lower hs0 hsmalltime hκ.le x y
  exact GaussianMixtureBand.bound μ ha hM hK hβ hβ1 hh (fun p=>C p) m hCov hm data
    (hdata.mono (𝓕.le v) le_rfl) (Output m)
    (NativeFrozenGaussianLaw.law 𝓕 μ v b hvb P Λ κ hκ hκP sides (parameters θ η) (centers x y)
      hΛ hsmall H hbH data hdata J hb0 hb1 hnull B hBDG hJ hlocal m hm) hc σ hσ hr j

end SHE.NativeFrozenBandCovariance
