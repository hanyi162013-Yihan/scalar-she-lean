module

public import SHE.FiniteItoPastRandomSmoothFormula
public import SHE.FiniteItoSmoothResidual

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.FiniteItoSmoothAnalytic
open Set MeasureTheory PredictableL2 FiniteItoNoise GaussianItoTest StoppedItoInputs Filter Topology
open scoped NNReal ENNReal
variable {Ω X C : Type*} [MeasurableSpace Ω]
variable [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
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
    (hvc : v≤c) (hcH : c≤H) (hG : ∀ x,LocalizedItoTest.SmoothTimeTest v c (G x) (dG x))
    (Kcap : Fin n→ℝ) (hKcap : ∀ i,0≤Kcap i)
    (hRcap : ∀ i,∀ᵐ p∂energyMeasure μ H,‖R i p‖^2≤Kcap i)
    (hGp : ∀ t,Continuous (fun p : X×WordRecursion.State n=>G p.1 t p.2))
    (hHp : ∀ t,Continuous (fun p : X×WordRecursion.State n=>GaussianTaylor.hessian (G p.1 t) p.2))
    (hdGp : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),Continuous (fun p : X×WordRecursion.State n=>dG p.1 t p.2))
    (B : ℝ) (hB0 : 0≤B) (hB : ∀ x t z,‖GaussianTaylor.hessian (G x t) z‖≤B)
    (m : ℝ→ℝ) (hm : IntervalIntegrable m volume v c)
    (hm0 : ∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),0≤m t)
    (hmb : ∀ x,∀ᵐ t∂volume.restrict (Ioc (v:ℝ) (c:ℝ)),∀ z,‖dG x t z‖≤m t*(1+‖z‖))
    {u : Ω→X} (hu : StronglyMeasurable[𝓕 v] u) :
    ∀ᵐ ω ∂μ,G (u ω) c (Y (c,ω))=G (u ω) v (Y (v,ω))+
      J.integral (inp hu.measurable) ω+
      ∫ t in (v:ℝ)..(c:ℝ),FiniteItoParameterResidual.drift Y D G dG (u ω) ω t := by
  have hK:=FiniteItoSmoothResidual.continuous_residual 𝓕 μ H Y hcontY R Kcap hKcap hRcap
    v c hvc hcH G dG hG hGp hHp hdGp B hB0 hB m hm hm0 hmb
  exact FiniteItoPastRandomSmoothFormula.formula 𝓕 μ H Y hY R J G dG hgm hpc L hL0 hL v c e
    hJ hlocal z hcontY hRep hvc hcH hG hK hu

end SHE.FiniteItoSmoothAnalytic
