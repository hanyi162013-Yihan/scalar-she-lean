module

public import SHE.NativeItoBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The physical finite-dimensional Itô input is obtained from the
universal ordinary formula. Continuity/predictability of observations,
their integral representations, the actual gradient-noise term, and the
physical bracket are all supplied by proved native heat/Haar identities. -/
noncomputable section
namespace SHE.NativeObservationIto
open MeasureTheory Set PredictableL2 FiniteHaar DyadicApproximation StoppedFourier
open NativeHeatObservation NativeObservationNaturality PositiveGapObservations WordRecursion
open scoped NNReal ENNReal

theorem finiteItoInput_congr_path {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    {Y V : Ω → ℝ → WordRecursion.State n} {Γ : Ω → ℝ → Matrix (Fin n) (Fin n) ℝ}
    {a b : ℝ} {N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ}
    (hab : a ≤ b) (hIto : PhysicalIto.FiniteItoInput μ Y Γ a b N)
    (hEq : ∀ ω,∀ t ∈ Icc a b,Y ω t=V ω t) : PhysicalIto.FiniteItoInput μ V Γ a b N := by
  intro G dG hG
  filter_upwards [hIto G dG hG] with ω hω
  rw [hEq ω b ⟨hab,le_rfl⟩,hEq ω a ⟨le_rfl,hab⟩] at hω
  have he : (∫ t in a..b,dG t (Y ω t)+(1/2:ℝ)*
      GaussianTaylorAverage.covarianceAction (Γ ω t) (GaussianTaylor.hessian (G t) (Y ω t)))=
      ∫ t in a..b,dG t (V ω t)+(1/2:ℝ)*
      GaussianTaylorAverage.covarianceAction (Γ ω t) (GaussianTaylor.hessian (G t) (V ω t)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro t ht
    dsimp only
    rw [hEq ω t (Ioo_subset_Icc_self ht)]
  rw [he] at hω
  exact hω

variable {Ω : Type*} [MeasurableSpace Ω]
local instance nativeObservationIto_realSigma : MeasurableSpace RealL2 := borel RealL2
local instance nativeObservationIto_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeObservationIto_finiteExponent : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℝ≥0)
variable {ell M : ℝ} (hell : 0 < ell) (hM : 0 ≤ M)
variable (f : ℝ≥0 × Ω → EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable {n : ℕ} (Z : Fin n → Observation)
variable {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i,δ ≤ (Z i).target-(h:ℝ))
variable (U : ℝ≥0 × Ω → RealL2) (hU : StronglyMeasurable[𝓕.predictable] U)

def martingale (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (a b : ℝ) (G : ℝ → WordRecursion.State n → ℝ) : Lp ℝ 2 μ :=
  FiniteItoNoise.noise 𝓕 μ h (value δ Z U) (value_predictable 𝓕 δ Z U hU)
    (rows 𝓕 μ h hell hM f hf Z hδ hgap) J a b G

theorem martingale_centered (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (a b : ℝ) (G : ℝ → WordRecursion.State n → ℝ) :
    (∫ ω,martingale 𝓕 μ h hell hM f hf Z hδ hgap U hU J a b G ω ∂μ)=0 :=
  FiniteItoNoise.noise_centered 𝓕 μ h _ _ _ J a b G

theorem martingale_integrable (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (a b : ℝ) (G : ℝ → WordRecursion.State n → ℝ) :
    Integrable (martingale 𝓕 μ h hell hM f hf Z hδ hgap U hU J a b G) μ :=
  (Lp.memLp _).integrable (by norm_num : (1:ENNReal) ≤ 2)

theorem native_finiteItoInput
    (I : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ h)
    (J : StandardTerminalIto (C := RealHaarInput) (E := ℝ) 𝓕 μ h)
    (hIJ : StandardScalarNaturality I J) (hJ : StandardFiniteIto.Universal 𝓕 μ h J)
    (u : RealL2) (hc : ∀ ω,Continuous (fun t => U (t,ω)))
    (v : ℝ≥0 → Process (E := RealHaarIntegrand.Columns) 𝓕 μ h)
    (hv : ∀ t : ℝ≥0,t ≤ h → v t =ᵐ[energyMeasure μ h]
      (fun p => kernel ell M hell ((t:ℝ)-(p.1:ℝ),f p)))
    (hmild : ∀ (t : ℝ≥0),t ≤ h → ∀ᵐ ω ∂μ,U (t,ω)=heat t u+I.integral (v t) ω)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (h:ℝ)) :
    PhysicalIto.FiniteItoInput μ (fun ω t => value δ Z U (t.toNNReal,ω))
      (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b
      (fun G ω => martingale 𝓕 μ h hell hM f hf Z hδ hgap U hU J a b G ω) := by
  have hi := StandardFiniteIto.finiteItoInput 𝓕 μ h J hJ (rows 𝓕 μ h hell hM f hf Z hδ hgap)
    (initial Z u) (value δ Z U) (value_predictable 𝓕 δ Z U hU)
    (fun ω => value_continuous δ Z U (hc ω))
    (integral_representation 𝓕 μ h hell hM f hf Z hδ hgap I J hIJ u U v hv hmild) ha hab hb
  exact NativeItoBracket.finiteItoInput_of_density 𝓕 μ h hell hM f hf Z hδ hgap ha hab hb _ _ hi

include hδ hgap in
theorem value_eq_observe (X : Ω → ℝ × HeatCircle → ℝ) (ω : Ω) {t : ℝ}
    (ht0 : 0 ≤ t) (hth : t ≤ (h:ℝ)) :
    value δ Z U (t.toNNReal,ω)=observe (fun r => embed (U (r.toNNReal,ω))) (X ω) Z t := by
  ext i
  have hg : δ ≤ (Z i).target-t := (hgap i).trans (sub_le_sub_left hth _)
  have htarget : t < (Z i).target := by linarith
  change coordinate δ (Z i).target (Z i).center U (t.toNNReal,ω)=
    if t < (Z i).target then PhysicalProfile.physicalHeatMean (embed (U (t.toNNReal,ω)))
      ((Z i).target-t,(Z i).center) else X ω (t,(Z i).center)
  rw [ite_eq_left htarget,coordinate_eq_functional hδ U _ _
    (by simpa only [Real.coe_toNNReal _ ht0] using hg),Real.coe_toNNReal _ ht0,
    functional_physical (sub_pos.mpr htarget)]

include hδ hgap in
/-- The original physical observation process satisfies the ordinary
finite-dimensional Itô formula, once the concrete native input above is
instantiated. The terminal field version is unused because the window
has an explicitly positive heat gap. -/
theorem physical_finiteItoInput (X : Ω → ℝ × HeatCircle → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (h:ℝ))
    (N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (hi : PhysicalIto.FiniteItoInput μ (fun ω t => value δ Z U (t.toNNReal,ω))
      (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b N) :
    PhysicalIto.FiniteItoInput μ
      (fun ω => observe (fun r => embed (U (r.toNNReal,ω))) (X ω) Z)
      (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b N := by
  apply finiteItoInput_congr_path μ hab hi
  intro ω t ht
  exact value_eq_observe h Z hδ hgap U X ω (ha.trans ht.1) (ht.2.trans hb)

include hδ hgap in
/-- All original stopping times remain visible. The unmasked density is
valid precisely because the whole Itô window precedes every original
stop. Arbitrary asynchronous stops outside this window are not collapsed. -/
theorem stopped_finiteItoInput (X : Ω → ℝ × HeatCircle → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (h:ℝ))
    (hstop : ∀ i,b ≤ (Z i).stop)
    (N : (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (hi : PhysicalIto.FiniteItoInput μ (fun ω t => value δ Z U (t.toNNReal,ω))
      (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b N) :
    PhysicalIto.FiniteItoInput μ
      (fun ω => PhysicalIto.stoppedObserve (fun r => embed (U (r.toNNReal,ω))) (X ω) Z)
      (fun ω t => CovarianceMatrix.densityMatrix (NativeItoBracket.coefficient f ω) Z t) a b N := by
  have hp := physical_finiteItoInput (μ := μ) (h := h) (f := f) (Z := Z)
    (hδ := hδ) (hgap := hgap) (U := U) X ha hab hb N hi
  apply finiteItoInput_congr_path μ hab hp
  intro ω t ht
  exact (PhysicalIto.stoppedObserve_eq _ _ Z (fun i => ht.2.trans (hstop i))).symm

end SHE.NativeObservationIto
