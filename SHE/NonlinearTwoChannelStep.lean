module

public import SHE.LocalTwoChannelIto
public import SHE.AdditiveHaarForcing
public import SHE.PredictableScalarField

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option Elab.async false
noncomputable section

namespace SHE.NonlinearTwoChannelStep
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality WordRecursion CovarianceEndpoint OrthogonalItoChannels
open scoped NNReal ENNReal
local instance nonlinearTwoChannelStep_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nonlinearTwoChannelStep_nativePeriod : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance nonlinearTwoChannelStep_realSigma : MeasurableSpace RealL2 := borel _
local instance nonlinearTwoChannelStep_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nonlinearTwoChannelStep_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nonlinearTwoChannelStep_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nonlinearTwoChannelStep_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nonlinearTwoChannelStep_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

theorem constant_native_ae (κ : ℝ) (hκ : 0 < κ) :
    (fun x => (CircleNormalization.push (AdditiveHaarForcing.constantField κ hκ).1 x).re)=ᵐ[
      AddCircle.haarAddCircle (T := 2*Real.pi)] (fun _ => κ) := by
  have hc := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (AdditiveHaarForcing.constantField_ae κ hκ)
  filter_upwards [CircleNormalization.push_ae (AdditiveHaarForcing.constantField κ hκ).1,hc] with x hx hc
  rw [hx,hc]
  rfl

theorem densityMatrix_add {n : ℕ} (c d : ℝ × HeatCircle → ℝ) (hc : Measurable c) (hd : Measurable d)
    (Z : Fin n → Observation) {δ M N s t : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hgap : ∀ i,δ ≤ (Z i).target-s) (ht : t ≤ s)
    (hcB : ∀ x,|c (t,x)| ≤ M) (hdB : ∀ x,|d (t,x)| ≤ N) :
    CovarianceMatrix.densityMatrix c Z t+CovarianceMatrix.densityMatrix d Z t=
      CovarianceMatrix.densityMatrix (fun p => c p+d p) Z t := by
  ext i j
  change (∫ x : HeatCircle,c (t,x)*heatRow Z t x i*heatRow Z t x j ∂AddCircle.haarAddCircle)+
      (∫ x : HeatCircle,d (t,x)*heatRow Z t x i*heatRow Z t x j ∂AddCircle.haarAddCircle)=_
  rw [← integral_add (CovarianceMatrix.covariance_spatial_integrable c hc Z hδ hM hgap ht hcB i j)
    (CovarianceMatrix.covariance_spatial_integrable d hd Z hδ hN hgap ht hdB i j)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable (κ : ℝ) (hκ : 0 < κ) {ell M : ℝ} (hell : 0 < ell)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (U : ℝ≥0 × Ω → RealL2) (hU : StronglyMeasurable[𝓕.predictable] U)
variable (a : ℝ → ℝ) (ha : Measurable a) (hbounds : ∀ z,ell ≤ a z ∧ a z ≤ M)
variable (hcoef : ∀ p : ℝ≥0 × Ω,(f p).1=CoefficientFields.coefficient a ha M
  (NonlinearHaarIntegrand.absBound hell hbounds) (U p))

include hU hcoef in
/-- The actual additive and residual Haar row covariances add to the
literal TOTAL scalar variance κ+a(X), after spatial AE identification. -/
theorem density_sum_eq {n : ℕ} (Z : Fin n → Observation) {b δ t : ℝ}
    (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-b) (ht : t ≤ b) (ω : Ω) :
    CovarianceMatrix.densityMatrix
        (NativeItoBracket.coefficient (fun _ : ℝ≥0 × Ω => AdditiveHaarForcing.constantField κ hκ) ω) Z t+
      CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t=
    CovarianceMatrix.densityMatrix (fun p => κ+a (PredictableScalarField.wordField U ω p)) Z t := by
  have h₀ : CovarianceMatrix.densityMatrix
        (NativeItoBracket.coefficient (fun _ : ℝ≥0 × Ω => AdditiveHaarForcing.constantField κ hκ) ω) Z t=
      CovarianceMatrix.densityMatrix (fun _ => κ) Z t := by
    ext i j
    apply integral_congr_ae
    filter_upwards [constant_native_ae κ hκ] with x hx
    change (CircleNormalization.push (AdditiveHaarForcing.constantField κ hκ).1 x).re*
        heatRow Z t x i*heatRow Z t x j=κ*heatRow Z t x i*heatRow Z t x j
    rw [hx]
  have h₁ : CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t=
      CovarianceMatrix.densityMatrix (fun p => a (PredictableScalarField.wordField U ω p)) Z t := by
    ext i j
    apply integral_congr_ae
    have he := PredictableScalarField.nativeField_coefficient_ae a ha M
      (NonlinearHaarIntegrand.absBound hell hbounds) U (t.toNNReal,ω)
    filter_upwards [he] with x hx
    change (CircleNormalization.push (f (t.toNNReal,ω)).1 x).re*heatRow Z t x i*heatRow Z t x j=
      a (PredictableScalarField.nativeField U ((t.toNNReal,ω),x))*heatRow Z t x i*heatRow Z t x j
    rw [hcoef,hx]
  rw [h₀,h₁]
  exact densityMatrix_add _ _ measurable_const (ha.comp (PredictableScalarField.wordField_section_measurable 𝓕 hU ω))
    Z hδ hκ.le (hell.le.trans ((hbounds 0).1.trans (hbounds 0).2)) hgap ht
    (fun _ => by rw [abs_of_pos hκ]) (fun _ => NonlinearHaarIntegrand.absBound hell hbounds _)

include hf hU hcoef in
/-- The local Itô formula for the printed two-channel structure. The
ordinary scalar integral is over the direct sum of the original additive
and residual Haar noises. The native-clock mild equation is explicit. -/
theorem finiteItoInput
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ h J))
    (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ h J))
    (hJ : StandardFiniteIto.Universal 𝓕 μ h J)
    (u : RealL2) (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (v₀ v₁ : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv₀ : ∀ t : ℝ≥0,t ≤ h → v₀ t=ᵐ[energyMeasure μ h]
      (fun p => kernel κ κ hκ ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)))
    (hv₁ : ∀ t : ℝ≥0,t ≤ h → v₁ t=ᵐ[energyMeasure μ h]
      (fun p => kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)))
    (hmild : ∀ t : ℝ≥0,t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=
      NativeHeatObservation.heat (t:ℝ) u+I₀.integral (v₀ t) ω+I₁.integral (v₁ t) ω)
    {n : ℕ} (Z : Fin n → Observation) (b : ℝ≥0) (hb : b ≤ h)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(b:ℝ))
    {q : ℝ} (hq : 0 ≤ q) (hqb : q ≤ (b:ℝ)) :
    ∃ N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ,
      (∀ G,Integrable (N G) μ ∧ (∫ ω,N G ω ∂μ)=0) ∧
      PhysicalIto.FiniteItoInput μ
        (fun ω => observe (fun r => embed (U (r.toNNReal,ω))) (PredictableScalarField.wordField U ω) Z)
        (fun ω t => CovarianceMatrix.densityMatrix
          (fun p => κ+a (PredictableScalarField.wordField U ω p)) Z t) q b N := by
  obtain ⟨N,hN,hi⟩ := LocalTwoChannelIto.finiteItoInput 𝓕 μ h hκ hκ.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    hell (hell.le.trans ((hbounds 0).1.trans (hbounds 0).2)) f hf Z b hδ hgap
    hnull I₀ I₁ J hIJ₀ hIJ₁ hJ u U hc v₀ v₁ hv₀ hv₁ hmild hb hq hqb (PredictableScalarField.wordField U)
  refine ⟨N,hN,fun G dG hG => ?_⟩
  filter_upwards [hi G dG hG] with ω hω
  rw [hω]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hqb
  intro t ht
  dsimp only
  rw [density_sum_eq 𝓕 κ hκ hell f U hU a ha hbounds hcoef Z hδ hgap ht.2.le ω]

include hf hU hcoef in
/-- The exact physical one-step recursion for separate common additive
and residual noises. Its insertion uses total variance κ+a; all channel
brackets and centered stochastic terms have been derived above. -/
theorem one_step
    (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ h J))
    (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ h J))
    (hJ : StandardFiniteIto.Universal 𝓕 μ h J)
    (u : RealL2) (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (v₀ v₁ : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv₀ : ∀ t : ℝ≥0,t ≤ h → v₀ t=ᵐ[energyMeasure μ h]
      (fun p => kernel κ κ hκ ((t:ℝ)-(p.1:ℝ),AdditiveHaarForcing.constantField κ hκ)))
    (hv₁ : ∀ t : ℝ≥0,t ≤ h → v₁ t=ᵐ[energyMeasure μ h]
      (fun p => kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)))
    (hmild : ∀ t : ℝ≥0,t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=
      NativeHeatObservation.heat (t:ℝ) u+I₀.integral (v₀ t) ω+I₁.integral (v₁ t) ω)
    {n : ℕ} (W : EndpointWindow n) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i,δ ≤ (W.observations i).target-W.right)
    (hleft : 0 ≤ W.left) (hright : W.right ≤ (h:ℝ))
    {F : WordRecursion.State n → ℝ} (hF : ContDiff ℝ 2 F) {C L B K : ℝ}
    (hbound : ∀ z,‖F z‖ ≤ C) (hD : ∀ z,‖fderiv ℝ F z‖ ≤ L)
    (hDD : ∀ z,‖GaussianTaylor.hessian F z‖ ≤ B) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hH : ∀ z w,‖GaussianTaylor.hessian F w-GaussianTaylor.hessian F z‖ ≤ K*‖w-z‖) :
    ∃ ζ : Ω → ℝ,Integrable ζ μ ∧ (∫ ω,ζ ω ∂μ)=0 ∧ ∀ᵐ ω ∂μ,
      F (observe (fun r => embed (U (r.toNNReal,ω))) (PredictableScalarField.wordField U ω) W.observations W.right)=
        gaussianSemigroup W.coefficient W.observations W.left W.right F
          (observe (fun r => embed (U (r.toNNReal,ω))) (PredictableScalarField.wordField U ω) W.observations W.left)+ζ ω+
        PhysicalIto.wordRemainder W (fun z => κ+a z)
          (fun r => embed (U (r.toNNReal,ω))) (PredictableScalarField.wordField U ω) F := by
  let b : ℝ≥0 := W.right.toNNReal
  have hbcoe : (b:ℝ)=W.right := Real.coe_toNNReal _ (hleft.trans W.ordered)
  have hbh : b ≤ h := by exact_mod_cast (show (b:ℝ) ≤ h by rw [hbcoe]; exact hright)
  have hgapb : ∀ i,δ ≤ (W.observations i).target-(b:ℝ) := by simpa only [hbcoe] using hgap
  have horder : W.left ≤ (b:ℝ) := by rw [hbcoe]; exact W.ordered
  obtain ⟨N,hN,hi⟩ := finiteItoInput 𝓕 μ h κ hκ hell f hf U hU a ha hbounds hcoef
    hnull I₀ I₁ J hIJ₀ hIJ₁ hJ u hc v₀ v₁ hv₀ hv₁ hmild W.observations b hbh hδ hgapb hleft horder
  rw [hbcoe] at hi
  refine ⟨N (GaussianItoTest.backward W F),(hN _).1,(hN _).2,?_⟩
  apply PhysicalIto.physical_one_step μ W (fun z => κ+a z) (measurable_const.add ha)
    (fun ω r => embed (U (r.toNNReal,ω))) (PredictableScalarField.wordField U)
    (Filter.Eventually.of_forall (PredictableScalarField.wordField_section_measurable 𝓕 hU))
    (add_nonneg hκ.le (hell.le.trans ((hbounds 0).1.trans (hbounds 0).2)))
    (fun z => (abs_add_le _ _).trans (add_le_add (by rw [abs_of_pos hκ])
      (NonlinearHaarIntegrand.absBound hell hbounds z)))
    N hi hF hbound hD hDD hB hK hH

end SHE.NonlinearTwoChannelStep
