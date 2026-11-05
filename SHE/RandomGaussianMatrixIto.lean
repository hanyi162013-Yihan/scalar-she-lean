module
public import SHE.GaussianMatrixFamily
public import SHE.FiniteItoEnergyAnalytic
public import SHE.FiniteItoRandomCentering

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SHE.GaussianMatrixFamily.value SHE.GaussianMatrixFamily.derivative SHE.GaussianMatrixCurve.backward SHE.GaussianMatrixCurve.timeDerivative
set_option maxHeartbeats 1800000
namespace SHE.RandomGaussianMatrixIto
open Set MeasureTheory ProbabilityTheory PredictableL2 Filter GaussianMatrixFamily
open GaussianTaylorAverage GaussianConvolution GaussianTaylor
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H v b : ℝ≥0)
variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable {n : ℕ} (R : Fin n → Process (E:=C) 𝓕 μ H)
variable (Y : ℝ≥0 × Ω → WordRecursion.State n) (hY : StronglyMeasurable[𝓕.predictable] Y)
variable (S : Family X n) (hv : S.left=(v:ℝ)) (hb : S.right=(b:ℝ))

include hY hv hb in
/-- The random-parameter Gaussian backward formula also applies when
the actual bracket differs from the reference density. The resulting
covariance defect is retained in the original finite Ito drift. -/
theorem formula (e : X)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J)
    (z₀ : WordRecursion.State n)
    (hcont : ∀ ω,Continuous (fun t=>Y (t,ω)))
    (hrep : ∀ t:ℝ≥0,t≤H→(fun ω=>Y (t,ω))=ᵐ[μ] StandardFiniteIto.vectorIntegral 𝓕 μ H J z₀ R t)
    (hvb : v≤b) (hbH : b≤H)
    (majorant : ℝ→ℝ) (hmi : IntervalIntegrable majorant volume v b)
    (hm0 : ∀ t∈Ioo (v:ℝ) (b:ℝ),0≤majorant t)
    (hmb : ∀ p,∀ t∈Ioo (v:ℝ) (b:ℝ),∀ i j,|(S.curve p).density t i j|≤majorant t)
    {F : WordRecursion.State n→ℝ} (hF : SmoothCylinders.BoundedSmooth F)
    (L : ℝ) (hL0 : 0≤L) (hL : ∀ p t z,‖fderiv ℝ (value S F p t) z‖≤L)
    {u : Ω→X} (hu : StronglyMeasurable[𝓕 v] u) :
    ∀ᵐ ω ∂μ,value S F (u ω) b (Y (b,ω))=value S F (u ω) v (Y (v,ω))+
      J.integral (FiniteItoBorelGradient.input 𝓕 μ H Y hY R (value S F)
        (gradient_measurable S F hF) L hL0 hL v b e hu.measurable) ω+
      ∫ t in (v:ℝ)..(b:ℝ),FiniteItoParameterResidual.drift Y
        (StandardFiniteIto.rowCovariance 𝓕 μ H R) (value S F) (derivative S F) (u ω) ω t := by
  let G:=value S F
  let dG:=derivative S F
  have hgm:=gradient_measurable S F hF
  have hpc (t:ℝ) (z:WordRecursion.State n):Continuous (fun p:X=>fderiv ℝ (G p t) z):=
    (gradient_parameter_continuous S F hF t).comp (continuous_id.prodMk continuous_const)
  have hs:=uniform_value S F hF
  obtain ⟨B,hB0,hBb⟩:=hs.fderiv.fderiv.norm_bound
  have hB:∀p t z,‖hessian (G p t) z‖≤B:=fun p t z=>hBb (p,t) z
  let M:ℝ→ℝ:=fun t=>(1/2:ℝ)*(n:ℝ)^2*B*majorant t
  have hM0:∀t∈Ioo (v:ℝ) (b:ℝ),0≤M t:=fun t ht=>by
    dsimp [M]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hB0) (hm0 t ht)
  have hDb:∀p,∀t∈Ioo (v:ℝ) (b:ℝ),∀z,‖dG p t z‖≤M t:=by
    intro p t ht z
    have hact:=GaussianItoTest.action_entry_bound ((S.curve p).density t) (hessian (G p t) z)
      (hm0 t ht) (hmb p t ht)
    unfold dG derivative GaussianMatrixCurve.timeDerivative
    have he:GaussianMatrixCurve.backward (S.curve p) (shifted S F p) t=G p t:=by
      funext w
      unfold G value
      rfl
    rw [he]
    rw [norm_mul,norm_neg,Real.norm_eq_abs,abs_of_pos (by norm_num:(0:ℝ)<1/2)]
    have hh:=mul_le_mul_of_nonneg_left (hB p t z)
      (mul_nonneg (by norm_num:(0:ℝ)≤1/2) (mul_nonneg (sq_nonneg (n:ℝ)) (hm0 t ht)))
    have ha:=mul_le_mul_of_nonneg_left hact (by norm_num:(0:ℝ)≤1/2)
    rw [Real.norm_eq_abs] at ha
    dsimp [M]
    nlinarith only [hh,ha]
  have hM : IntervalIntegrable M volume v b:=hmi.const_mul _
  have hmAE:∀ᵐt:ℝ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),0≤M t:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    exact hM0 t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
  have hdAE (p:X):∀ᵐt:ℝ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)),∀z,‖dG p t z‖≤M t*(1+‖z‖):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    have hto:t∈Ioo (v:ℝ) (b:ℝ):=⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    intro z
    exact (hDb p t hto z).trans (le_mul_of_one_le_right (hM0 t hto) (by nlinarith [norm_nonneg z]))
  have hG (p:X):LocalizedItoTest.SmoothTimeTest v b (G p) (dG p):=by
    have hh:=smoothTimeTest S F hF p
    rwa [hv,hb] at hh
  exact FiniteItoEnergyAnalytic.formula 𝓕 μ H Y hY R J G dG hgm hpc L hL0 hL v b e
    hJ hlocal z₀ hcont hrep hvb hbH hG
    (fun t=>value_parameter_continuous S F hF t)
    (fun t=>hessian_parameter_continuous S F hF t)
    (by simpa only [hv,hb] using derivative_parameter_continuous S F hF)
    B hB0 hB M hM hmAE hdAE hu

include hY hv hb in
/-- Conditional Gaussian transition for the ACTUAL F_v-dependent Gram
curve. The random test is derived by finite past-simple approximation
inside the original finite-Itô theorem; no random-law substitution is
assumed. -/
theorem conditional_smooth (e : X)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J)
    (z₀ : WordRecursion.State n)
    (hcont : ∀ ω,Continuous (fun t=>Y (t,ω)))
    (hrep : ∀ t:ℝ≥0,t≤H→(fun ω=>Y (t,ω))=ᵐ[μ] StandardFiniteIto.vectorIntegral 𝓕 μ H J z₀ R t)
    (hvb : v≤b) (hbH : b≤H)
    (majorant : ℝ→ℝ) (hmi : IntervalIntegrable majorant volume v b)
    (hm0 : ∀ t∈Ioo (v:ℝ) (b:ℝ),0≤majorant t)
    (hmb : ∀ p,∀ t∈Ioo (v:ℝ) (b:ℝ),∀ i j,|(S.curve p).density t i j|≤majorant t)
    {u : Ω→X} (hu : StronglyMeasurable[𝓕 v] u)
    (hstart : (fun ω=>Y (v,ω))=ᵐ[μ] fun _=>0)
    (hcov : ∀ᵐ ω∂μ,∀ᵐ t:ℝ,t∈Ioo (v:ℝ) (b:ℝ)→
      StandardFiniteIto.rowCovariance 𝓕 μ H R ω t=(S.curve (u ω)).density t)
    {F : WordRecursion.State n→ℝ} (hF : SmoothCylinders.BoundedSmooth F)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ω in A,F (Y (b,ω)+S.center (u ω)) ∂μ)=
      ∫ω in A,gaussianAverage ((S.curve (u ω)).path (v:ℝ)).val F (S.center (u ω)) ∂μ := by
  let G:=value S F
  let dG:=derivative S F
  have hgm:=gradient_measurable S F hF
  have hs:=uniform_value S F hF
  obtain ⟨L,hL0,hLb⟩:=hs.fderiv.norm_bound
  have hL:∀p t z,‖fderiv ℝ (G p t) z‖≤L:=fun p t z=>hLb (p,t) z
  have hform:=formula 𝓕 μ H v b J R Y hY S hv hb e hJ hlocal z₀ hcont hrep hvb hbH
    majorant hmi hm0 hmb hF L hL0 hL hu
  have hcenter:=FiniteItoRandomCentering.centered 𝓕 μ H Y hY R G hgm L hL0 hL v b e J hlocal hu.measurable
  have hzero : ∀ᵐω∂μ,(∫t in (v:ℝ)..(b:ℝ),FiniteItoParameterResidual.drift Y
      (StandardFiniteIto.rowCovariance 𝓕 μ H R) G dG (u ω) ω t)=0:=by
    filter_upwards [hcov] with ω hω
    apply intervalIntegral.integral_zero_ae
    filter_upwards [hω,volume.ae_ne (b:ℝ)] with t ht hne htin
    rw [uIoc_of_le (show (v:ℝ)≤(b:ℝ) by exact_mod_cast hvb)] at htin
    have hto:t∈Ioo (v:ℝ) (b:ℝ):=⟨htin.1,lt_of_le_of_ne htin.2 hne⟩
    unfold FiniteItoParameterResidual.drift dG derivative GaussianMatrixCurve.timeDerivative
    rw [ht hto]
    have he:GaussianMatrixCurve.backward (S.curve (u ω)) (shifted S F (u ω)) t=G (u ω) t:=by
      funext w
      unfold G value
      rfl
    rw [he]
    ring
  have hsli (t:ℝ≥0):Measurable (fun ω=>Y (t,ω)):=
    (hY.mono (predictable_le_product 𝓕)).measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C,hC0,hCb⟩:=hs.norm_bound
  have hqi:Integrable (fun ω=>G (u ω) v (Y (v,ω))) μ:=by
    apply (integrable_const C).mono'
      ((value_measurable S F hF).comp
        (((hu.measurable.mono (𝓕.le v) le_rfl).prodMk measurable_const).prodMk (hsli v))).aestronglyMeasurable
    exact Eventually.of_forall (fun ω=>hCb (u ω,(v:ℝ)) (Y (v,ω)))
  have hGt (p:X) (z:WordRecursion.State n):G p b z=F (z+S.center p):=by
    change value S F p b z=F (z+S.center p)
    rw [value_eq]
    have ht:((S.curve p).path (b:ℝ)).val=0:=by
      rw [←hb,←S.right_eq p]
      exact (S.curve p).terminal
    simp only [ht,gaussianAverage,CovarianceMatrix.multivariateGaussian_zero_covariance,integral_dirac,add_zero]
  have heq : (fun ω=>F (Y (b,ω)+S.center (u ω)))=ᵐ[μ] fun ω=>
      G (u ω) v (Y (v,ω))+
        J.integral (FiniteItoBorelGradient.input 𝓕 μ H Y hY R G hgm L hL0 hL v b e hu.measurable) ω:=by
    filter_upwards [hform,hzero] with ω hf hz
    change G (u ω) b (Y (b,ω))=G (u ω) v (Y (v,ω))+
      J.integral (FiniteItoBorelGradient.input 𝓕 μ H Y hY R G hgm L hL0 hL v b e hu.measurable) ω+
      ∫ t in (v:ℝ)..(b:ℝ),FiniteItoParameterResidual.drift Y
        (StandardFiniteIto.rowCovariance 𝓕 μ H R) G dG (u ω) ω t at hf
    rw [hGt,hz,add_zero] at hf
    exact hf
  rw [integral_congr_ae (ae_restrict_of_ae heq),integral_add hqi.integrableOn hcenter.1.integrableOn,hcenter.2 A hA,add_zero]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hstart] with ω hω
  change G (u ω) v (Y (v,ω))=_
  rw [hω]
  change value S F (u ω) v 0=_
  rw [value_eq,zero_add]

end SHE.RandomGaussianMatrixIto
