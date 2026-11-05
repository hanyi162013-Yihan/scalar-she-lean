module

public import SHE.FiniteItoBorelGradient

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.FiniteItoBorelRandomFormula
open Set MeasureTheory PredictableL2 FiniteItoNoise GaussianItoTest StoppedItoInputs Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n)
variable (hY : StronglyMeasurable[𝓕.predictable] Y) (R : Fin n→Process (E:=C) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable (G dG : X→ℝ→WordRecursion.State n→ℝ)
variable (hgm : Measurable (fun p : X×(ℝ×WordRecursion.State n)=>fderiv ℝ (G p.1 p.2.1) p.2.2))
variable (hpc : ∀ t z,Continuous (fun x=>fderiv ℝ (G x t) z))
variable (L : ℝ) (hL0 : 0≤L) (hL : ∀ x t z,‖fderiv ℝ (G x t) z‖≤L)
variable (v c : ℝ≥0) (e : X)
local notation "D" => StandardFiniteIto.rowCovariance 𝓕 μ H R
local notation "K" => FiniteItoParameterResidual.residual Y D v c G dG
local notation "g" => FiniteItoGradientFamily.raw 𝓕 μ H Y R G c
local notation "hg" => FiniteItoBorelGradient.measurable_raw 𝓕 μ H Y hY R G hgm c
local notation "major" => FiniteItoGradientMajorant.process 𝓕 μ H R L
local notation "hb" => FiniteItoGradientFamily.bound 𝓕 μ H Y R G c L hL0 hL
local notation "inp" => FiniteItoBorelGradient.input 𝓕 μ H Y hY R G hgm L hL0 hL v c e

include hpc in
/-- Ordinary deterministic finite-dimensional Itô plus ordinary
past-event locality yields the genuine random-past-parameter formula.
The noise is the actual diagonal gradient input of the SAME integral J;
parameter continuity of the analytic residual remains an explicit and
separately provable hypothesis. -/
theorem formula (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal : StandardTerminalPastLocality J) (z : WordRecursion.State n)
    (hcontY : ∀ ω,Continuous (fun t=>Y (t,ω)))
    (hRep : ∀ t:ℝ≥0,t≤H→(fun ω=>Y (t,ω))=ᵐ[μ] StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t)
    (hvc : v≤c) (hcH : c≤H) (hG : ∀ x,RegularTest v c (G x) (dG x))
    (hK : ∀ᵐ ω ∂μ,Continuous (fun x=>K x ω))
    {u : Ω→X} (hu : StronglyMeasurable[𝓕 v] u) :
    ∀ᵐ ω ∂μ,G (u ω) c (Y (c,ω))=G (u ω) v (Y (v,ω))+
      J.integral (inp hu.measurable) ω+
      ∫ t in (v:ℝ)..(c:ℝ),FiniteItoParameterResidual.drift Y D G dG (u ω) ω t := by
  have hfixed (x : X) : K x=ᵐ[μ] J.integral
      (PastParameterItoInput.input 𝓕 μ H v g hg major hb e (measurable_const (a:=x))) := by
    have hf := hJ.formula R z Y hY hcontY hRep v.2 (by exact_mod_cast hvc)
      (by exact_mod_cast hcH) (G x) (dG x) (hG x)
    have hgrad := regular_admissible (hG x)
    rw [show PastParameterItoInput.input 𝓕 μ H v g hg major hb e (measurable_const (a:=x))=
      inp (measurable_const (a:=x)) from rfl,
      FiniteItoBorelGradient.constant_input_eq 𝓕 μ H Y hY R G hgm L hL0 hL v c e x hgrad,
      ←FiniteItoPastNoise.noise_eq_post 𝓕 μ H Y hY R J v c hvc (G x) hgrad]
    filter_upwards [hf] with ω hω
    simp only [NNReal.val_eq_coe,Real.toNNReal_coe] at hω
    dsimp only [FiniteItoParameterResidual.residual,FiniteItoParameterResidual.drift]
    simpa only [Real.toNNReal_coe] using (by linarith :
      G x c (Y (c,ω))-G x v (Y (v,ω))-
        ∫ t in (v:ℝ)..(c:ℝ),dG x t (Y (t.toNNReal,ω))+(1/2:ℝ)*
          GaussianTaylorAverage.covarianceAction (D ω t)
            (GaussianTaylor.hessian (G x t) (Y (t.toNNReal,ω)))=
        noise 𝓕 μ H Y hY R J v c (G x) ω)
  have he := PastParameterItoIdentity.diagonal_identity 𝓕 μ H v g hg major hb e J hlocal
    (FiniteItoBorelGradient.continuous_parameter 𝓕 μ H Y R G c hpc) K hfixed hK hu
  filter_upwards [he] with ω hω
  change K (u ω) ω=J.integral (inp hu.measurable) ω at hω
  dsimp only [FiniteItoParameterResidual.residual] at hω
  simp only [NNReal.val_eq_coe,Real.toNNReal_coe] at hω
  simpa only [Real.toNNReal_coe] using (by linarith :
    G (u ω) c (Y (c,ω))=G (u ω) v (Y (v,ω))+J.integral (inp hu.measurable) ω+
      ∫ t in (v:ℝ)..(c:ℝ),FiniteItoParameterResidual.drift Y D G dG (u ω) ω t)

end SHE.FiniteItoBorelRandomFormula
