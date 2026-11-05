module

public import SHEStochastic.ScalarLipschitzPicardStep
public import SHEStochastic.ScalarLipschitzIntegratedComparison
public import SHEStochastic.ScalarLipschitzFourierMild

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzFixedPoint
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzKernelBounds ScalarLipschitzConvolution ScalarLipschitzItoMoment ScalarLipschitzRawBounds
  ScalarLipschitzDampedEnergy ScalarLipschitzDampedMoments ScalarLipschitzMomentBall
  ScalarLipschitzPicardStep ScalarLipschitzIntegratedComparison
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "tm" => PredictableL2.timeMeasure
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)

local notation "Proc" => Process (E := RealL2) F μ H
local notation "S" => PredictableExponential.scale F μ H

theorem unscale_weighted (γ : ℝ) (D : ℝ) (z : Ball (F := F) (μ := μ) (H := H) D) :
    ∀ᵐ t ∂tm H,weightedMoment (μ := μ) γ (fun s ω => S γ z.val (s,ω)) t≤ENNReal.ofReal D := by
  have hZ : ∀ᵐ t ∂tm H,moment 16 (fun ω => z.val (t,ω)) μ≤ENNReal.ofReal D := z.property
  filter_upwards [hZ,scaled_fibre γ (S γ z.val)] with t ht he
  rw [←he,PredictableExponential.cancel]
  exact ht

structure Step (γ D : ℝ) (u₀ : RealL2) (U : ℝ≥0 → Ω → RealL2)
    (hU : StronglyMeasurable[F.predictable] (Function.uncurry U)) where
  path : ℝ≥0 → Ω → RealL2
  continuous : ∀ ω,Continuous (fun t => path t ω)
  adapted : StronglyAdapted F path
  bound : ∀ t, t≤H → weightedMoment (μ := μ) γ path t≤ENNReal.ofReal D
  equation : ∀ t, t≤H → ∃ hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H),
    path t=ᵐ[μ] fun ω => forcing u₀ t+(ito e P).integral (input e hg U hU t hE) ω

variable {e P hg}

theorem Step.predictable {γ D : ℝ} {u₀ : RealL2} {U : ℝ≥0 → Ω → RealL2}
    {hU : StronglyMeasurable[F.predictable] (Function.uncurry U)}
    (X : Step e P hg γ D u₀ U hU) :
    StronglyMeasurable[F.predictable] (Function.uncurry X.path) :=
  ContinuousPredictable.stronglyMeasurable F X.path X.adapted X.continuous

theorem Step.energy {γ D : ℝ} {u₀ : RealL2} {U : ℝ≥0 → Ω → RealL2}
    {hU : StronglyMeasurable[F.predictable] (Function.uncurry U)}
    (X : Step e P hg γ D u₀ U hU) (hγ : 0≤γ) :
    Integrable (fun p : ℝ≥0×Ω => ‖X.path p.1 p.2‖^2) (energyMeasure μ H) := by
  apply integrated X.predictable (D := (timeWeight (-γ) H)^8*ENNReal.ofReal D)
    (ENNReal.mul_ne_top (by unfold timeWeight; finiteness) ENNReal.ofReal_ne_top)
  filter_upwards [timeMeasure_ae_mem H] with t ht
  rw [weightedMoment_unweight γ X.path t]
  apply mul_le_mul
  · apply pow_le_pow_left'
    unfold timeWeight
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have htH : (t : ℝ)≤(H : ℝ) := by exact_mod_cast ht.2
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr htH)]
  · exact X.bound t ht.2
  · exact bot_le
  · exact bot_le

def Step.class {γ D : ℝ} {u₀ : RealL2} {U : ℝ≥0 → Ω → RealL2}
    {hU : StronglyMeasurable[F.predictable] (Function.uncurry U)}
    (X : Step e P hg γ D u₀ U hU) (hγ : 0≤γ) : Proc :=
  processOf X.path X.predictable (X.energy hγ)

theorem Step.class_ae {γ D : ℝ} {u₀ : RealL2} {U : ℝ≥0 → Ω → RealL2}
    {hU : StronglyMeasurable[F.predictable] (Function.uncurry U)}
    (X : Step e P hg γ D u₀ U hU) (hγ : 0≤γ) :
    X.class hγ=ᵐ[energyMeasure μ H] Function.uncurry X.path :=
  processOf_ae X.path X.predictable (X.energy hγ)

theorem Step.map_mem {γ D : ℝ} {u₀ : RealL2} {U : ℝ≥0 → Ω → RealL2}
    {hU : StronglyMeasurable[F.predictable] (Function.uncurry U)}
    (X : Step e P hg γ D u₀ U hU) (hγ : 0≤γ) :
    S (-γ) (X.class hγ)∈Ball D := by
  change ∀ᵐ t ∂tm H,moment 16 (fun ω => S (-γ) (X.class hγ) (t,ω)) μ≤_
  filter_upwards [timeMeasure_ae_mem H,scaled_fibre γ (X.class hγ),
    Measure.ae_ae_of_ae_prod (X.class_ae hγ)] with t ht h₁ h₂
  rw [h₁,weightedMoment,moment_congr h₂]
  exact X.bound t ht.2

variable (e P hg)

def step (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    {γ D : ℝ} (hγ : 0<γ) (hD : 1≤D)
    (hsmall : (2 : ℝ)^16*growthConstant g (C : ℝ) (H : ℝ) γ≤1/4)
    (u₀ : RealL2) (h₀ : 2*(2 : ℝ)^16*‖u₀‖^16≤D)
    (z : Ball (F := F) (μ := μ) (H := H) D) :
    Step e P hg γ D u₀ (fun t ω => S γ z.val (t,ω)) (Lp.stronglyMeasurable _) := by
  let u := S γ z.val
  have hh := exists_step e P hg hH hn hγ hD hsmall u₀ h₀ (fun t ω => u (t,ω))
    (Lp.stronglyMeasurable u) (unscale_weighted γ D z)
  exact ⟨Classical.choose hh,(Classical.choose_spec hh).1,(Classical.choose_spec hh).2.1,
    (Classical.choose_spec hh).2.2.1,(Classical.choose_spec hh).2.2.2⟩

theorem contract_steps {γ D : ℝ} (hγ : 0<γ)
    (hsmall : heatConstant (H : ℝ)*(C : ℝ)^2*BieleckiKernel.mass γ≤1/4)
    (u₀ : RealL2) (a b : Ball (F := F) (μ := μ) (H := H) D)
    (X : Step e P hg γ D u₀ (fun t ω => S γ a.val (t,ω)) (Lp.stronglyMeasurable _))
    (Y : Step e P hg γ D u₀ (fun t ω => S γ b.val (t,ω)) (Lp.stronglyMeasurable _)) :
    ‖S (-γ) (X.class hγ.le)-S (-γ) (Y.class hγ.le)‖ ≤ (1/2 : ℝ)*‖a.val-b.val‖ := by
  let u := S γ a.val
  let v := S γ b.val
  have hX := (X.predictable.mono (predictable_le_product F)).measurable
  have hY := (Y.predictable.mono (predictable_le_product F)).measurable
  have hEq := integrated e P hg (fun t ω => u (t,ω)) (fun t ω => v (t,ω))
    (Lp.stronglyMeasurable _) (Lp.stronglyMeasurable _) hγ X.path Y.path hX hY
  have h := hEq (by
    filter_upwards [timeMeasure_ae_mem H] with t ht
    obtain ⟨hEU,hE⟩ := X.equation t ht.2
    obtain ⟨hEV,hE'⟩ := Y.equation t ht.2
    refine ⟨hEU,hEV,?_⟩
    filter_upwards [hE,hE'] with ω hω hω'
    rw [hω,hω',add_sub_add_left_eq_sub])
  have ha : X.class hγ.le-Y.class hγ.le =ᵐ[energyMeasure μ H]
      (fun p => X.path p.1 p.2-Y.path p.1 p.2) := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub (X.class hγ.le) (Y.class hγ.le)),
      X.class_ae hγ.le,Y.class_ae hγ.le] with p h₁ h₂ h₃
    rw [h₁,Pi.sub_apply,h₂,h₃]
    rfl
  have hb : u-v =ᵐ[energyMeasure μ H] (fun p => u (p.1,p.2)-v (p.1,p.2)) := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub u v)] with p hp
    exact hp
  rw [←class_energy γ (X.class hγ.le-Y.class hγ.le) X.path Y.path ha,
    ←class_energy γ (u-v) (fun t ω => u (t,ω)) (fun t ω => v (t,ω)) hb,
    PredictableExponential.sub,PredictableExponential.sub] at h
  dsimp only [u,v] at h
  rw [PredictableExponential.cancel,PredictableExponential.cancel] at h
  let A := heatConstant (H : ℝ)*(C : ℝ)^2*BieleckiKernel.mass γ
  have hA : 0≤A := mul_nonneg (mul_nonneg (heatConstant_nonneg H.property) (sq_nonneg (C : ℝ)))
    (BieleckiKernel.mass_nonneg hγ.le)
  have hn : ‖S (-γ) (X.class hγ.le)-S (-γ) (Y.class hγ.le)‖^2 ≤ A*‖a.val-b.val‖^2 := by
    change _ ≤ ENNReal.ofReal A*ENNReal.ofReal (‖a.val-b.val‖^2) at h
    rw [←ENNReal.ofReal_mul hA] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA (sq_nonneg _))).mp h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  exact (hn.trans (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))).trans_eq (by ring)

end SHEStochastic.ScalarLipschitzFixedPoint
