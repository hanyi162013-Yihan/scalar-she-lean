module

public import SHEStochastic.ScalarLipschitzFixedPoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzNativeExistence
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzKernelBounds ScalarLipschitzConvolution ScalarLipschitzDampedMoments
  ScalarLipschitzMomentBall ScalarLipschitzPicardStep ScalarLipschitzFixedPoint
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]

local instance : MeasurableSpace (HilbertColumns.Space I RealL2) := borel _
local instance : BorelSpace (HilbertColumns.Space I RealL2) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)

local notation "Proc" => Process (E := RealL2) F μ H
local notation "S" => PredictableExponential.scale F μ H

omit [DecidableEq I] [IsProbabilityMeasure μ] in
theorem input_congr (U V : ℝ≥0 → Ω → RealL2)
    (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hV : StronglyMeasurable[F.predictable] (Function.uncurry V))
    (hUV : Function.uncurry U=ᵐ[energyMeasure μ H] Function.uncurry V)
    (t : ℝ≥0) (hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H)) :
    ∃ hE' : Integrable (fun p => ‖raw e hg V t p‖^2) (energyMeasure μ H),
      input e hg U hU t hE=input e hg V hV t hE' := by
  have he : raw e hg U t=ᵐ[energyMeasure μ H] raw e hg V t := by
    filter_upwards [hUV] with p hp
    exact congrArg (fun a => ScalarLipschitzHeatColumns.kernel e ((t : ℝ)-(p.1 : ℝ)) (coefficient hg a)) hp
  refine ⟨hE.congr (he.fun_comp (fun c => ‖c‖^2)),?_⟩
  apply PastItoAlgebra.eq_of_ambient_ae F μ H
  exact (input_ae e hg U hU t hE).trans (he.trans (input_ae e hg V hV t _).symm)

theorem initial (U : ℝ≥0 → Ω → RealL2) (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hE : Integrable (fun p => ‖raw e hg U 0 p‖^2) (energyMeasure μ H)) :
    (ito e P).integral (input e hg U hU 0 hE)=0 := by
  have hz : input e hg U hU 0 hE=0 := by
    apply PastItoAlgebra.eq_of_ambient_ae F μ H
    filter_upwards [input_ae e hg U hU 0 hE,ae_eq_of_ae_eq_trim (Lp.coeFn_zero
      (α := ℝ≥0×Ω) (E := HilbertColumns.Space I RealL2) (p := 2)
      (μ := (energyMeasure μ H).trim (predictable_le_product F)))] with p h₁ h₂
    rw [h₁,h₂]
    exact raw_zero e hg U 0 (show (0 : ℝ≥0)≤p.1 from zero_le)
  rw [hz,map_zero]

/-- The nonlinear scalar white-noise heat convolution has a continuous
predictable fixed point on any null-complete native Brownian space.
The initial value may be any deterministic L² class. -/
theorem exists_mild (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ) (u₀ : RealL2) :
    ∃ (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W)),
      (∀ ω,Continuous (fun t => W t ω)) ∧
      Integrable (fun p : ℝ≥0×Ω => ‖W p.1 p.2‖^2) (energyMeasure μ H) ∧
      (W 0=ᵐ[μ] fun _ => u₀) ∧
      ∀ t, t≤H → ∃ hE : Integrable (fun p => ‖raw e hg W t p‖^2) (energyMeasure μ H),
        W t=ᵐ[μ] fun ω => forcing u₀ t+(ito e P).integral (input e hg W hW t hE) ω := by
  obtain ⟨γ,hγ,hcon,hsmall⟩ := weight_choice (H := H) (C := C) (g := g)
  let D := max 1 (2*(2 : ℝ)^16*‖u₀‖^16)
  have hD : 1≤D := le_max_left _ _
  have h₀ : 2*(2 : ℝ)^16*‖u₀‖^16≤D := le_max_right _ _
  let T := Ball (F := F) (μ := μ) (H := H) D
  let _ : Nonempty T := ⟨⟨0,zero_mem D⟩⟩
  let _ : CompleteSpace T := (isClosed_ball D).completeSpace_coe
  let Φ (z : T) : T :=
    let X := step e P hg hH hn hγ hD hsmall u₀ h₀ z
    ⟨S (-γ) (X.class hγ.le),X.map_mem hγ.le⟩
  have hΦ : ContractingWith (1/2 : ℝ≥0) Φ := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro a b
    change dist ((Φ a).val : Proc) (Φ b).val≤(1/2 : ℝ)*dist (a.val : Proc) b.val
    rw [dist_eq_norm,dist_eq_norm]
    exact contract_steps e P hg hγ hcon u₀ a b _ _
  let z := hΦ.fixedPoint Φ
  let X := step e P hg hH hn hγ hD hsmall u₀ h₀ z
  let U : ℝ≥0 → Ω → RealL2 := fun t ω => S γ z.val (t,ω)
  have hU : StronglyMeasurable[F.predictable] (Function.uncurry U) := Lp.stronglyMeasurable _
  have hz : S (-γ) (X.class hγ.le)=z.val := congrArg Subtype.val hΦ.fixedPoint_isFixedPt
  have hp : X.class hγ.le=S γ z.val := by
    exact (PredictableExponential.cancel' F μ H γ (X.class hγ.le)).symm.trans (congrArg (S γ) hz)
  have hEq : Function.uncurry U=ᵐ[energyMeasure μ H] Function.uncurry X.path := by
    have he := X.class_ae hγ.le
    rw [hp] at he
    exact he
  have hFix (t : ℝ≥0) (ht : t≤H) :
      ∃ hE : Integrable (fun p => ‖raw e hg X.path t p‖^2) (energyMeasure μ H),
        X.path t=ᵐ[μ] fun ω => forcing u₀ t+(ito e P).integral (input e hg X.path X.predictable t hE) ω := by
    obtain ⟨hE,he⟩ := X.equation t ht
    obtain ⟨hE',he'⟩ := input_congr e hg U X.path hU X.predictable hEq t hE
    exact ⟨hE',by rw [←he']; exact he⟩
  refine ⟨X.path,X.predictable,X.continuous,X.energy hγ.le,?_,hFix⟩
  obtain ⟨hE,he⟩ := hFix 0 zero_le
  filter_upwards [he,Lp.coeFn_zero (α := Ω) (E := RealL2) (p := 2) (μ := μ)] with ω hω hz
  rw [hω,initial e P hg X.path X.predictable hE,show (0 : Lp RealL2 2 μ) ω=0 from hz,add_zero,forcing]
  change RealHeat.realHeat ((0 : ℝ)/NativeHeatObservation.timeScale) u₀=u₀
  rw [zero_div,RealHeat.realHeat_zero,ContinuousLinearMap.id_apply]

include P in
/-- Strong zero-drift existence in the exact stopped Fourier
form used by the Girsanov argument. -/
theorem exists_zero (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2) :
    ∃ M : ScalarCanonicalObservation.Model H hg zero_lt_one le_rfl b u₀ Ω I,
      M.μ=μ ∧ M.F=F ∧ M.basis=e ∧ M.W 0=ᵐ[M.μ] fun _ => u₀ := by
  obtain ⟨W,hW,hc,hE,hi,hFix⟩ := exists_mild e P hg hH hn u₀
  have hEI (t : ℝ≥0) (ht : t≤H) : Integrable (fun p => ‖raw e hg W t p‖^2) (energyMeasure μ H) :=
    (hFix t ht).choose
  have he := ScalarLipschitzFourierMild.stopped e P hg W hW b u₀ hc hn hE hEI
    (fun t ht => (hFix t ht).choose_spec)
  exact ⟨⟨μ,F,W,hW,hc,hn,P,e,he⟩,rfl,rfl,rfl,hi⟩

end SHEStochastic.ScalarLipschitzNativeExistence
