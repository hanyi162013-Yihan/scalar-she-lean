module

public import SHE.JointGammaTestFields
public import SHE.EndpointAffineDerivativeBound

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.JointGammaDerivativeEnvelope
open Set MeasureTheory ControlledProfile SmoothCylinders GaussianItoTest GaussianIncrement
open scoped NNReal ENNReal
local instance jointGammaDerivativeEnvelope_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance jointGammaDerivativeEnvelope_sigma : MeasurableSpace StoppedFourier.CircleL2 := borel _
local instance jointGammaDerivativeEnvelope_borel : BorelSpace StoppedFourier.CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ)
variable (v b : ℝ≥0) (hvb : v≤b) {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) {F : WordRecursion.State n→ℝ} (hF : BoundedSmooth F)
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
local notation "L" => (fun _ : ℝ=>JointGammaAffine.current n Λ θ (fun i=>(Z i).target))
local notation "DL" => (fun _ : ℝ=>(0:FirstGammaAffine.Space n→L[ℝ]WordRecursion.State n))
local notation "R" => FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)

include hΛ hF in
/-- A single endpoint-integrable envelope controls the actual time
chain for EVERY random past input, despite unbounded original states. -/
theorem uniform_envelope : ∃ m : ℝ→ℝ,IntervalIntegrable m volume v b ∧
    (∀ t∈Ioc (v:ℝ) (b:ℝ),0≤m t) ∧
    ∀ p:Inputs,∀ t∈Ioo (v:ℝ) (b:ℝ),∀ z:FirstGammaAffine.Space n,
      ‖JointGammaTestFields.derivative P Λ θ v b hvb Z htarget F p t z‖≤m t*(1+‖z‖) := by
  obtain ⟨M,hM⟩:=hF.norm_bound
  obtain ⟨A,hA⟩:=hF.fderiv.norm_bound
  obtain ⟨B,hB⟩:=hF.fderiv.fderiv.norm_bound
  have hA0 : 0≤A:=(norm_nonneg _).trans (hA 0)
  have hB0 : 0≤B:=(norm_nonneg _).trans (hB 0)
  let D:ℝ:=0
  have hD0 : 0≤D:=by positivity
  let C:=fun t:ℝ=>(n:ℝ)^2*B*(P.upper*(1+StoppedFourier.heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))))
  have hCint : IntervalIntegrable C volume v b:=
    (CovarianceEndpoint.endpoint_majorant_integrable P.upper).const_mul _
  refine ⟨fun t=>C t+A*D,hCint.add intervalIntegrable_const,?_,?_⟩
  · intro t ht
    have hr : 0≤((b:ℝ)-t)^(-(1/2:ℝ)):=Real.rpow_nonneg (sub_nonneg.mpr ht.2) _
    have hC0 : 0≤C t:=mul_nonneg (mul_nonneg (sq_nonneg _) hB0)
      (mul_nonneg P.upper_nonneg (add_nonneg zero_le_one (mul_nonneg StoppedFourier.heatConstant_pos.le hr)))
    exact add_nonneg hC0 (mul_nonneg hA0 hD0)
  · intro p t ht z
    have hd : ‖DL t‖≤D := by simp only [norm_zero,D,le_refl]
    have hc:=EndpointAffineDerivativeBound.bound (W p) hF hA0 hB0 hD0 hM hA hB L DL ht hd z
    have hr:=EndpointAffineDerivativeBound.bound (W p) hF hA0 hB0 (le_refl (0:ℝ)) hM hA hB
      (fun _=>R) (fun _=>0) ht (by simpa only [norm_zero] using (le_refl (0:ℝ))) z
    change ‖GaussianEndpointAffine.derivative (W p) F L DL (fun _=>0) (fun _=>0) t z-
      GaussianEndpointAffine.derivative (W p) F (fun _=>R) (fun _=>0) (fun _=>0) (fun _=>0) t z‖≤_
    exact (norm_sub_le _ _).trans ((add_le_add hc hr).trans (by
      change (_+A*D)*(1+‖z‖)+(_+A*0)*(1+‖z‖)≤(C t+A*D)*(1+‖z‖)
      dsimp [C,ControlledReferenceWindows.window]
      ring_nf
      exact le_rfl))

end SHE.JointGammaDerivativeEnvelope
