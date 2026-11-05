module
public import SHE.MixedPastCompleteCovarianceMoments

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.MixedPastBoundedCovarianceInput
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores PhysicalProfile
open scoped NNReal ENNReal BigOperators
local instance mixedPastBoundedCovarianceInput_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastBoundedCovarianceInput_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastBoundedCovarianceInput_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastBoundedCovarianceInput_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastBoundedCovarianceInput_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastBoundedCovarianceInput_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastBoundedCovarianceInput_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastBoundedCovarianceInput_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
variable {Ω X:Type*}[MeasurableSpace Ω][MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable {n d r m:ℕ}

include hIJ₀ hIJ₁ in
/-- A newest input may depend on the actual current sample, rather
than being measurable at the old past. A deterministic cap of its true
score mass is sufficient: only the honest conditional offset budget is
averaged, and the newest coefficient error stays outside every Gaussian. -/
theorem input_moment (νX:Measure X)[SFinite νX](P:CanonicalCovariance.ProfileParameters)
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ){θ:ℝ}(hθ:|θ|≤1)
    (v q:ℝ≥0)(hvq:v≤q)(hqH:q≤H)(hspan:(q:ℝ)-(v:ℝ)≤1)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i)(hσ1:∀i,σ i≤1)(hages:∀i,σ i≤target i)
    (hgap:∀i,(q:ℝ)-(v:ℝ)<target i)
    (lo hi:Fin r→ℝ)(hlo:∀j,(q:ℝ)-(v:ℝ)≤lo j)(hlohi:∀j,lo j<hi j)
    (hstop:∀j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint:∀j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (D:Fin r→State n)
    (hD:∀ω j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ
        (MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)
        (MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v ω)) lo hi j)).range)
    (row:X→State n)(hrow:Measurable row)
    (g:Fin d→Fin n)(leaf:Fin m→Fin n)
    (hnative:∀j,σ (leaf j)=target (leaf j))(ht:∀j,target (leaf j)∈Ioc 0 P.horizon)
    (F:State d→ℝ)(hFm:Measurable F){A0 ν:ℝ}(hA0:0≤A0)(hν:0≤ν)
    (hf:ContDiff ℝ r F)(hfb:∀j,j≤r→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b:ℕ)(hb:0<b)(B0:ℝ≥0)(hBDG:StandardTerminalBDGPower (b*(m+2)) J B0)
    (e:Ω×X→ℝ)(he:Measurable e)(K Ecap:ℝ)(hK:0≤K)(hEcap:0≤Ecap):
    let U:=MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let dir:=MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
    let mean:=MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
    let B:=fun ω=>ControlledFixedReserve.covariance P Λ (U ω) (dir ω)
      (fixedProfile P Λ (U ω) (dir ω) lo hi) σ target center ((q:ℝ)-(v:ℝ)) θ
    (∀ω,(B ω).PosSemidef)→
    (∀ω,∀ᵐx∂νX,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (B ω)).range)→
    (∀ω,Integrable (fun x=>|e (ω,x)| *scoreVariance (B ω) (row x)) νX)→
    (∀ω,(∫x,|e (ω,x)| *scoreVariance (B ω) (row x) ∂νX)≤Ecap)→
    (∀ω,|∏j,scoreVariance (familyCovariance σ target center (referenceProfile P Λ (U ω) (dir ω)) lo hi j) (D j)|≤K)→
    let G:=fun ω=>(1/2:ℝ)*∫x,e (ω,x)*PointwiseCompleteGaussianWord.value P Λ (U ω) (dir ω) θ ((q:ℝ)-(v:ℝ))
      σ target center lo hi (mean ω) true D (row x) g leaf F ∂νX
    Integrable (fun ω=>|G ω|^(2*b)) μ ∧
      (∫ω,|G ω|^(2*b) ∂μ)≤MixedPastWordMoments.momentConstant P r m b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent)*
          (K*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν*Ecap/2)^(2*b) := by
  intro U dir mean B hB hrowRange hEnergy hMass hgeom G
  let budget:=fun ω=>currentBudget P Λ (U ω) (dir ω) θ target center leaf (mean ω) b
  let T:=MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
  let Rcap:=K*T*Ecap/2
  have hT:0≤T:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hC:=MixedPastCompleteOffsetWeights.constant_with_past_weight (r:=r)
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspan σ target center leaf hnative (fun j=>(ht j).1) (fun j=>hgap (leaf j))
    b hb B0 hBDG (fun _=>1) measurable_const (fun _=>zero_le_one) (integrable_const (1:ℝ))
  have hCi:Integrable (fun ω=>MixedPastWordMoments.momentConstant P r m b (budget ω)) μ:=by
    simpa only [one_mul,budget] using hC.1
  have hCb:(∫ω,MixedPastWordMoments.momentConstant P r m b (budget ω) ∂μ)≤
      MixedPastWordMoments.momentConstant P r m b
        ((m:ℝ)*(NativeHybridMoments.momentConstant (b*(m+2)) B0 κ M)^P.exponent):=by
    simpa only [one_mul,budget,integral_const,probReal_univ,one_smul,mul_one] using hC.2
  have hU:Measurable U:=(MixedPastJointData.pastU_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hdir:Measurable dir:=(MixedPastJointData.pastD_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v) le_rfl
  have hm:=MixedPastJointData.mean_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center
  have hG:Measurable G:=by
    let cs:=assignments (m:=m+1) (List.finRange r)
    have hinner:Measurable (fun z:Ω×X=>PointwiseCompleteGaussianWord.value P Λ (U z.1) (dir z.1)
        θ ((q:ℝ)-(v:ℝ)) σ target center lo hi (mean z.1) true D (row z.2) g leaf F):=by
      change Measurable (fun z:Ω×X=>(1/2:ℝ)^r*
        ((cs.map (fun choices=>fibreAverage P Λ (U z.1) (dir z.1) θ ((q:ℝ)-(v:ℝ))
          σ target center lo hi (mean z.1) true D (row z.2) g leaf choices F)).sum))
      have heq(z:Ω×X):(cs.map (fun choices=>fibreAverage P Λ (U z.1) (dir z.1) θ ((q:ℝ)-(v:ℝ))
          σ target center lo hi (mean z.1) true D (row z.2) g leaf choices F)).sum=
        ∑j:Fin cs.length,fibreAverage P Λ (U z.1) (dir z.1) θ ((q:ℝ)-(v:ℝ))
          σ target center lo hi (mean z.1) true D (row z.2) g leaf (cs.get j) F:=
        FiniteAssignmentMoments.map_sum_eq_fin cs _
      simp_rw [heq]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j _
      exact VaryingControlledGaussianFields.fibreAverage_measurable P Λ θ ((q:ℝ)-(v:ℝ))
        (fun z:Ω×X=>U z.1) (fun z:Ω×X=>dir z.1) (hU.comp measurable_fst) (hdir.comp measurable_fst)
        σ target center lo hi (fun z:Ω×X=>mean z.1) (hm.comp measurable_fst) true
        (fun _=>D) (fun _=>measurable_const) (fun z:Ω×X=>row z.2) (hrow.comp measurable_snd)
        g leaf (cs.get j) F hFm
    exact (((he.mul hinner).stronglyMeasurable.integral_prod_right').measurable).const_mul _
  have hp(ω:Ω):|G ω|^(2*b)≤MixedPastWordMoments.momentConstant P r m b (budget ω)*Rcap^(2*b):=by
    have hh:=PointwiseCompleteCovarianceInput.bound νX P Λ (U ω) (dir ω) θ
      ((q:ℝ)-(v:ℝ)) (sub_nonneg.mpr (by exact_mod_cast hvq)) σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint (mean ω) D (hD ω) row hrow (hB ω) (hrowRange ω)
      g leaf hnative ht F hFm hA0 hν hf hfb b hb
      (fun x=>e (ω,x)) (he.comp (measurable_const.prodMk measurable_id)) (hEnergy ω) K hK (hgeom ω)
    have hmass0:0≤∫x,|e (ω,x)| *scoreVariance (B ω) (row x) ∂νX:=
      integral_nonneg_of_ae ((hrowRange ω).mono (fun x hx=>mul_nonneg (abs_nonneg _) (scoreVariance_nonneg (hB ω) hx)))
    have hpow:(((1/2:ℝ)*K*T)*∫x,|e (ω,x)| *scoreVariance (B ω) (row x) ∂νX)^(2*b)≤Rcap^(2*b):=by
      apply pow_le_pow_left₀ (mul_nonneg (by positivity) hmass0)
      exact (mul_le_mul_of_nonneg_left (hMass ω) (by positivity : 0≤(1/2:ℝ)*K*T)).trans_eq (by dsimp only [Rcap];ring)
    exact hh.trans (mul_le_mul_of_nonneg_left hpow (MixedPastWordMoments.momentConstant_nonneg _ _ _ _ _))
  have hgi:Integrable (fun ω=>|G ω|^(2*b)) μ:=(hCi.mul_const (Rcap^(2*b))).mono'
    ((continuous_abs.measurable.comp hG).pow_const _).aestronglyMeasurable
      (ae_of_all _ (fun ω=>by simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using hp ω))
  refine ⟨hgi,?_⟩
  have hi:=integral_mono hgi (hCi.mul_const (Rcap^(2*b))) hp
  rw [integral_mul_const] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_right hCb ((even_two_mul b).pow_nonneg _)).trans_eq (by
    dsimp only [Rcap,T] <;> ring))

end SHE.MixedPastBoundedCovarianceInput
