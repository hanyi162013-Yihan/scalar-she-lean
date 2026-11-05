module

public import SHEStochastic.MatrixUnboundedPointIncrements
public import SHEStochastic.MatrixPointFieldTightness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedPointTightness
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open HeatParameterCover HeatParameterCoordinates
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
variable {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0) (hH : (H : ℝ)≤1)

def value (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (R : ℝ≥0) (N : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (p : Parameter) (i : Fin n) : Lp ℝ 2 μ :=
  (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
    (MatrixUnboundedPointIncrements.input G hG hβ ell hell hLower F U hU μ H hH R p i)

/-- Existing bounded-cutoff versions retain the actual point field and
zero initial trace. Uniformity in the cutoff is proved separately below. -/
theorem exists_version (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (R : ℝ≥0) (N : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode)) (i : Fin n) :
    ∃ Y : Ω → C(Parameter,ℝ),Measurable Y ∧
      (∀ p,(fun ω => Y ω p)=ᵐ[μ] value G hG hβ ell hell hLower F H hH μ U hU R N p i) ∧
      ∀ᵐ ω ∂μ,∀ p,Y ω (zeroTime p)=0 :=
  MatrixPointFieldTightness.exists_version F μ H (NativeMatrixEquation.cap (G_R R))
    (NativeMatrixEquation.cap_nonneg (G_R R)) (NativeMatrixEquation.profile F (G_R R) U hU)
    (fun _ => le_rfl) hH (NativeMatrixEquation.profile_measurable F (G_R R) U hU) N i

include hβ1 in
/-- L2-localized cutoff fields are jointly tight with no bound on the
coefficient truncation radii. Both the solution laws and their coupled
Brownian realizations may vary; all vector components stay coupled. -/
theorem exists_tight_versions (μ : ℕ → Measure Ω) [∀ m,IsProbabilityMeasure (μ m)]
    (U : ℕ → ℝ≥0×Ω → Physical (d := Fin n))
    (hU : ∀ m,StronglyMeasurable[F.predictable] (U m))
    (R : ℕ → ℝ≥0) (N : ∀ m,FiniteScalarIto.Family F (μ m) H (Fin n×SHE.FiniteHaar.HaarNode))
    (K : ℝ) (hbound : ∀ m,∀ᵐ z ∂energyMeasure (μ m) H,‖U m z‖≤K) :
    ∃ Y : ℕ → Ω → (Fin n → C(Parameter,ℝ)),
      (∀ m,Measurable (Y m)) ∧
      (∀ i m p,(fun ω => Y m ω i p)=ᵐ[μ m] value G hG hβ ell hell hLower F H hH (μ m) (U m) (hU m) (R m) (N m) p i) ∧
      (∀ m,∀ᵐ ω ∂μ m,∀ i p,Y m ω i (zeroTime p)=0) ∧
      IsTightMeasureSet (Set.range (fun m => (μ m).map (Y m))) := by
  choose Z hm he hz using fun (i : Fin n) (m : ℕ) =>
    exists_version G hG hβ ell hell hLower F H hH (μ m) (U m) (hU m) (R m) (N m) i
  have hbase := UnboundedHeatIncrementCaps.exponent_pos hβ1
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2/UnboundedHeatIncrementCaps.exponent β) (by norm_num : (1 : ℝ)<2)
  have hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ) := by
    have hh := (div_lt_iff₀ hbase).mp hk
    push_cast
    nlinarith
  let pwr : ℕ := 2*2^k
  let q : ℝ := UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)
  have hpwr : 0<pwr := by dsimp [pwr];positivity
  have hqr : 2<q := hq
  obtain ⟨a,ha,haq⟩ := exists_between (div_pos (sub_pos.mpr hqr) (show (0 : ℝ)<pwr from by exact_mod_cast hpwr))
  let α : ℝ≥0 := ⟨a,ha.le⟩
  let MC : ℝ≥0∞ := (NativeScalarBDG.constant k : ℝ≥0∞)*
    UnboundedGlobalJointMoments.jointConstant (fun z => ‖G z‖) C β K H^(2^k)
  have hMC : MC≠⊤ := by
    have hc := UnboundedGlobalJointMoments.jointConstant_finite (fun z => ‖G z‖) C β K H
    dsimp [MC]
    finiteness
  let M : ℝ≥0 := MC.toNNReal
  have hM : (M : ℝ≥0∞)=MC := ENNReal.coe_toNNReal hMC
  have ht (i : Fin n) : IsTightMeasureSet (Set.range (fun m => (μ m).map (Z i m))) := by
    let p₀ : Parameter := ⟨0,by simp [HeatParameterCover.region]⟩
    apply KolmogorovFieldTightness.tight μ (Z i) (hm i) (zeroTime p₀)
      (fun m => (hz i m).mono fun ω h => h p₀) parameter_cover (by norm_num) (by norm_num : (0 : ℝ)<2)
      (p := pwr) (q := q) (M := M) (α := α)
      (by exact_mod_cast hpwr) hqr (by exact ha) haq
    intro m
    apply BDGKolmogorov.of_nat_moments (μ m) (fun p ω => Z i m ω p)
      (fun p => (ContinuousMap.measurable_eval p).comp (hm i m)) pwr hpwr q (by linarith) M
    intro p q'
    calc
      _ = ∫⁻ ω,ENNReal.ofReal
          (‖value G hG hβ ell hell hLower F H hH (μ m) (U m) (hU m) (R m) (N m) p i ω-
            value G hG hβ ell hell hLower F H hH (μ m) (U m) (hU m) (R m) (N m) q' i ω‖^pwr) ∂μ m := by
        apply lintegral_congr_ae
        filter_upwards [he i m p,he i m q'] with ω hp hq
        rw [hp,hq]
      _ ≤ MC*edist p q'^q := MatrixUnboundedPointIncrements.native_moment G hG hβ hβ1 ell hell hLower
        F (U m) (hU m) (μ m) H hH (R m) p q' i (hbound m) (N m) k
      _ = _ := by rw [hM]
  let Y : ℕ → Ω → (Fin n → C(Parameter,ℝ)) := fun m ω i => Z i m ω
  have hY (m : ℕ) : Measurable (Y m) := measurable_pi_iff.mpr (fun i => hm i m)
  exact ⟨Y,hY,he,fun m => ae_all_iff.mpr (fun i => hz i m),
    FiniteMarginalTightness.tight_varying μ Y hY ht⟩

end SHEStochastic.MatrixUnboundedPointTightness
