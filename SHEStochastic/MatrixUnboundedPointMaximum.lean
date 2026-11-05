module

public import SHEStochastic.MatrixUnboundedPointTightness
public import SHEStochastic.KolmogorovFieldMaximum
public import SHEStochastic.SublinearHeatMomentScale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedPointMaximum
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open HeatParameterCover HeatParameterCoordinates
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
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

/-- Common increment moment constant for all coefficient cutoffs. -/
def momentConstant (K : ℝ) (k : ℕ) : ℝ≥0∞ :=
  (NativeScalarBDG.constant k : ℝ≥0∞)*
    UnboundedGlobalJointMoments.jointConstant (fun z => ‖G z‖) C β K H^(2^k)

theorem moment_finite (K : ℝ) (k : ℕ) : momentConstant G (C := C) (β := β) H K k≠⊤ := by
  have hc := UnboundedGlobalJointMoments.jointConstant_finite (fun z => ‖G z‖) C β K H
  dsimp [momentConstant]
  finiteness

include hβ in
/-- Its complete dependence on the localization radius is sublinear. -/
theorem moment_factor (K : ℝ) (k : ℕ) :
    momentConstant G (C := C) (β := β) H K k=
      momentConstant G (C := C) (β := β) H 0 k*
        SublinearHeatIntegratedEnergy.stateFactor K β^(2^k) := by
  unfold momentConstant
  rw [SublinearHeatMomentScale.joint_factor (fun z => ‖G z‖) C β hβ K H,mul_pow]
  ring

include hβ hβ1 in
/-- The checked localized increment moments are negligible relative to
the corresponding even-power exit thresholds as the radius increases. -/
theorem normalized_moment_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ => momentConstant G (C := C) (β := β) H (N : ℝ) k/(N : ℝ≥0∞)^(2*2^k))
      atTop (𝓝 0) := by
  have hp : 0<2^k := by positivity
  have hl := ENNReal.Tendsto.const_mul (a := momentConstant G (C := C) (β := β) H 0 k)
    (SublinearHeatMomentScale.normalized_tendsto β hβ1 (2^k) hp) (Or.inr (moment_finite G H 0 k))
  simp only [mul_zero] at hl
  apply hl.congr'
  apply Filter.Eventually.of_forall
  intro N
  dsimp only
  rw [moment_factor G hβ H (N : ℝ) k]
  have hdiv (A B : ℝ≥0∞) (p : ℕ) : (A/B)^p=A^p/B^p := by
    simpa only [ENNReal.rpow_natCast] using
      ENNReal.div_rpow_of_nonneg A B (z := (p : ℝ)) (Nat.cast_nonneg p)
  rw [hdiv,pow_mul]
  simp only [div_eq_mul_inv,mul_assoc]

include hβ1 in
/-- Explicit supremum tail bound for an actual continuous version of
the nonlinear cutoff-equation point convolution. The bound contains
only the original coefficient, localization radius and heat geometry. -/
theorem tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (R : ℝ≥0) (N : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode)) (i : Fin n)
    {K : ℝ} (hbound : ∀ᵐ z ∂energyMeasure μ H,‖U z‖≤K)
    (Y : Ω → C(Parameter,ℝ)) (hY : Measurable Y)
    (hrep : ∀ p,(fun ω => Y ω p)=ᵐ[μ]
      MatrixUnboundedPointTightness.value G hG hβ ell hell hLower F H hH μ U hU R N p i)
    (hzero : ∀ᵐ ω ∂μ,∀ p,Y ω (zeroTime p)=0)
    (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α L : ℝ≥0) (hα : 0<α) (hL : 0<L) :
    μ {ω | KolmogorovFieldMaximum.amplitude (T := Parameter) (2*2^k : ℕ) α L<‖Y ω‖} ≤
      (momentConstant G (C := C) (β := β) H K k*
        constL 64 2 (2*2^k : ℕ) (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) α)/(L : ℝ≥0∞) := by
  obtain ⟨D,hDcount,hDdense⟩ := TopologicalSpace.exists_countable_dense Parameter
  let p₀ : Parameter := ⟨0,by simp [HeatParameterCover.region]⟩
  let M : ℝ≥0 := (momentConstant G (C := C) (β := β) H K k).toNNReal
  have hM : (M : ℝ≥0∞)=momentConstant G (C := C) (β := β) H K k :=
    ENNReal.coe_toNNReal (moment_finite G H K k)
  have hX : IsKolmogorovProcess (fun p ω => Y ω p) μ (2*2^k : ℕ)
      (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) M := by
    apply BDGKolmogorov.of_nat_moments μ (fun p ω => Y ω p)
      (fun p => (ContinuousMap.measurable_eval p).comp hY) (2*2^k) (by positivity)
      (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) (by linarith) M
    intro p q
    calc
      _ = ∫⁻ ω,ENNReal.ofReal (‖MatrixUnboundedPointTightness.value G hG hβ ell hell hLower F H hH μ U hU R N p i ω-
          MatrixUnboundedPointTightness.value G hG hβ ell hell hLower F H hH μ U hU R N q i ω‖^(2*2^k)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hrep p,hrep q] with ω hp hq
        rw [hp,hq]
      _ ≤ momentConstant G (C := C) (β := β) H K k*edist p q^(UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) :=
        MatrixUnboundedPointIncrements.native_moment G hG hβ hβ1 ell hell hLower F U hU μ H hH R p q i hbound N k
      _ = _ := by rw [hM]
  have ht := KolmogorovFieldMaximum.tail μ Y hY (zeroTime p₀) (hzero.mono fun ω h => h p₀)
    D hDcount hDdense parameter_cover (by norm_num) (by positivity) hq hα hX L hL
  simpa only [hM] using ht

end SHEStochastic.MatrixUnboundedPointMaximum
