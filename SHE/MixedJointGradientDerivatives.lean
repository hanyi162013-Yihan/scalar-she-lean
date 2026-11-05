module
public import SHE.MixedJointGradientDirections
public import SHE.SmoothWords
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
namespace SHE.MixedJointGradientDerivatives
open MeasureTheory NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open MixedNativeJointObservations PhysicalMeanRange StoppedGaussianScore
open NativeJointColumnDirections
open scoped NNReal ENNReal
local instance mixedNativeJointPastIto_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeJointPastIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeJointPastIto_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeJointPastIto_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeJointPastIto_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeJointPastIto_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))


variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ)
variable {n:ℕ} (Z:Fin n→WordRecursion.Observation) (b:ℝ≥0)
variable (hgap:∀i,(b:ℝ)<(Z i).target) (hbH:b≤H)

local notation "Rows"=>rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b hgap hΛ
local notation "Y"=>MixedJointNamedIto.path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b
local notation "Target"=>(fun i=>(Z i).target)
local notation "Stop"=>(fun i=>(Z i).stop)
local notation "Center"=>(fun i=>NativeHeatSpan.unitCenter (Z i).center)
local notation "cU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "cV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "ColU"=>(fun p k=>CircleNormalization.push (globalHaarColumn k (cU p).1))
local notation "ColV"=>(fun p k=>CircleNormalization.push (globalHaarColumn k (cV p).1))
local notation "Col0"=>(fun k=>CircleNormalization.push (globalHaarColumn k (AdditiveHaarForcing.constantField κ hκ).1))

local notation "Pred"=>predictable_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z b hgap hnull hΛ hbH

/-- A genuine Frechet derivative equals the literal scalar derivative
in any given physical input direction. -/
theorem scalar_deriv (G:WordRecursion.State n→ℝ)(z e:WordRecursion.State n)
    (hG:DifferentiableAt ℝ G z):
    fderiv ℝ G z e=deriv (fun t:ℝ=>G (z+t•e)) 0:=by
  have hl:HasDerivAt (fun t:ℝ=>z+t•e) e 0:=by
    convert ((hasDerivAt_id (0:ℝ)).smul_const e).const_add z using 1 <;> simp only [id_eq,one_smul]
  have hG':HasFDerivAt G (fderiv ℝ G z) (z+(0:ℝ)•e):=by
    simpa only [zero_smul,add_zero] using hG.hasFDerivAt
  simpa only [zero_smul,add_zero,Function.comp_def] using (hG'.comp_hasDerivAt 0 hl).deriv.symm

/-- On the actual original time/sample event, the full predictable
finite-Ito input is the TWO full-word scalar derivative contributions.
The undamped U term is retained, rather than dropped from higher noise. -/
theorem process_derivatives_ae (G:ℝ→WordRecursion.State n→ℝ)
    (hG:FiniteItoNoise.AdmissibleGradient G)(hD:∀t,Differentiable ℝ (G t)):
    ∀ᵐp∂energyMeasure μ H,p.1<b → ∀k:HaarNode,
      left k (FiniteItoNoise.gradientProcess 𝓕 μ H Y Pred Rows G hG p)=
        deriv (fun t:ℝ=>G p.1 (Y p+t•currentDirection Target Center p.1 (Col0 k))) 0 ∧
      right k (FiniteItoNoise.gradientProcess 𝓕 μ H Y Pred Rows G hG p)=
        deriv (fun t:ℝ=>G p.1 (Y p+t•currentDirection Target Center p.1 (ColU p k))) 0+
        deriv (fun t:ℝ=>G p.1 (Y p+t•dampedDirection Stop Target Center p.1 Λ (ColV p k-ColU p k))) 0:=by
  have ha:=MixedJointGradientDirections.gradient_actions_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S hΛ Z b hgap G
  have hp:=FiniteItoNoise.gradientProcess_ae 𝓕 μ H Y Pred Rows G hG
  filter_upwards [ha,hp] with p ha hp hpb k
  rw [hp]
  constructor
  · rw [(ha hpb k).1,scalar_deriv _ _ _ ((hD p.1) (Y p))]
  · rw [(ha hpb k).2,map_add,scalar_deriv _ _ _ ((hD p.1) (Y p)),
      scalar_deriv _ _ _ ((hD p.1) (Y p))]

/-- Actual recursively generated backward smooth tests discharge the
state differentiability; this is not a new analytic input block. -/
theorem backward_derivatives_ae (W:CovarianceEndpoint.EndpointWindow n)
    {F:WordRecursion.State n→ℝ}(hF:SmoothCylinders.BoundedSmooth F):
    let G:=GaussianItoTest.backward W F
    let hG:=FiniteItoNoise.regular_admissible (SmoothWords.boundedSmooth_backward_regular W hF)
    ∀ᵐp∂energyMeasure μ H,p.1<b → ∀k:HaarNode,
      left k (FiniteItoNoise.gradientProcess 𝓕 μ H Y Pred Rows G hG p)=
        deriv (fun t:ℝ=>G p.1 (Y p+t•currentDirection Target Center p.1 (Col0 k))) 0 ∧
      right k (FiniteItoNoise.gradientProcess 𝓕 μ H Y Pred Rows G hG p)=
        deriv (fun t:ℝ=>G p.1 (Y p+t•currentDirection Target Center p.1 (ColU p k))) 0+
        deriv (fun t:ℝ=>G p.1 (Y p+t•dampedDirection Stop Target Center p.1 Λ (ColV p k-ColU p k))) 0:=by
  intro G hG
  exact process_derivatives_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ hnull hΛ Z b hgap hbH G hG
    (fun t=>(SmoothWords.backward_boundedSmooth W hF t).smooth.differentiable (by norm_num))
end SHE.MixedJointGradientDerivatives
