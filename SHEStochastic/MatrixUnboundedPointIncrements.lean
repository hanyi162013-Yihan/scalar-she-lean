module

public import SHEStochastic.MatrixUnboundedPointMoments
public import SHEStochastic.UnboundedGlobalJointMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixUnboundedPointIncrements
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R

/-- Scalar coefficient energy retains the matrix Holder seminorm. This
allows reuse of the existing sublinear heat increment calculus. -/
theorem norm_holder (R : ℝ≥0) : HolderWith C β (fun z => ‖(G_R R).value z‖) := by
  simpa only [NNReal.coe_one,NNReal.one_rpow,NNReal.rpow_one,mul_one,one_mul,Function.comp_def] using
    lipschitzWith_one_norm.holderWith.comp (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower R)

variable {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)

/-- The true rescaling of the vector state, with its norm unchanged. -/
def state (p : ℝ≥0×Ω) := VectorNativeHeatEndpoint.push (U p)

include hU in
theorem predictable : StronglyMeasurable[F.predictable] (state U) :=
  (VectorNativeHeatEndpoint.push (n := n)).continuous.comp_stronglyMeasurable hU

def family (R T : ℝ≥0) (x : HeatCircle) :=
  UnboundedHeatFamily.family F (state U) (predictable F U hU)
    (norm_holder G hG hβ ell hell hLower R) hβ hβ1 T x

/-- Each actual matrix row increment is dominated by the scalar
coefficient-energy row, not by a cutoff-dependent uniform covariance cap. -/
theorem domination (R T S : ℝ≥0) (x y : HeatCircle) (i : Fin n) (p : ℝ≥0×Ω) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row ((T : ℝ)-(p.1 : ℝ)) (NativeMatrixEquation.profile F (G_R R) U hU p) x i-
      MatrixPointHeatRows.row ((S : ℝ)-(p.1 : ℝ)) (NativeMatrixEquation.profile F (G_R R) U hU p) y i‖^2) ≤
        ENNReal.ofReal (‖family G hG hβ hβ1 ell hell hLower F U hU R T x p-
          family G hG hβ hβ1 ell hell hLower F U hU R S y p‖^2) := by
  have hb := MatrixPointSquareEnergy.native_difference_bound (NativeMatrixEquation.data F (G_R R) U hU p)
    (G_R R).value (U p) (NativeMatrixEquation.coefficient_ae F (G_R R) U hU p)
    ((T : ℝ)-(p.1 : ℝ)) ((S : ℝ)-(p.1 : ℝ)) x y i
  simpa only [family,UnboundedHeatFamily.difference_energy,state,norm_norm] using hb

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

include hβ1 in
/-- Uniform joint time-space bracket estimate for the original nonlinear
Haar rows. The coefficient radius R is absent from its right side. -/
theorem family_bracket (R : ℝ≥0) (p q : HeatParameterCover.Parameter) (i : Fin n) {K : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H,‖U z‖≤K) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal
      (‖MatrixPointHeatRows.row ((GlobalHeatParameter.time H p : ℝ)-(s : ℝ))
          (NativeMatrixEquation.profile F (G_R R) U hU (s,ω)) (HeatParameterCoordinates.center p) i-
        MatrixPointHeatRows.row ((GlobalHeatParameter.time H q : ℝ)-(s : ℝ))
          (NativeMatrixEquation.profile F (G_R R) U hU (s,ω)) (HeatParameterCoordinates.center q) i‖^2)
      ∂SHE.PredictableL2.timeMeasure H) ≤
        UnboundedGlobalJointMoments.jointConstant (fun z => ‖G z‖) C β K H*
          ENNReal.ofReal (dist p q^UnboundedHeatIncrementCaps.exponent β) := by
  have hstate : ∀ᵐ z ∂energyMeasure μ H,‖state U z‖≤K :=
    hbound.mono fun z hz => by simpa only [state,LinearIsometry.norm_map] using hz
  have hb := UnboundedGlobalJointMoments.family_bracket F (state U) (predictable F U hU)
    (norm_holder G hG hβ ell hell hLower R) hβ hβ1 μ H p q hstate
  filter_upwards [hb] with ω hω
  apply (lintegral_mono (fun s => domination G hG hβ hβ1 ell hell hLower F U hU R
    (GlobalHeatParameter.time H p) (GlobalHeatParameter.time H q)
    (HeatParameterCoordinates.center p) (HeatParameterCoordinates.center q) i (s,ω))).trans
  simpa only [family,UnboundedGlobalJointMoments.jointConstant,UnboundedGlobalIncrementCaps.timeConstant,
    UnboundedGlobalIncrementCaps.spaceConstant,norm_norm,MatrixUnboundedHeatRows.zero] using hω

variable (hH : (H : ℝ)≤1)

def input (R : ℝ≥0) (p : HeatParameterCover.Parameter) (i : Fin n) : Process (E := Input (d := Fin n)) F μ H :=
  MatrixUnboundedPointMoments.input G hG hβ ell hell hLower F U hU μ H hH R
    (GlobalHeatParameter.time H p) (GlobalHeatParameter.time_le_horizon H p) (HeatParameterCoordinates.center p) i

include hβ1 in
/-- The same joint increment bound holds for the selected predictable
input representatives, including their original shared Haar coordinates. -/
theorem input_bracket (R : ℝ≥0) (p q : HeatParameterCover.Parameter) (i : Fin n) {K : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H,‖U z‖≤K) :
    ∀ᵐ ω ∂μ,(∫⁻ s,ENNReal.ofReal
      (‖(input G hG hβ ell hell hLower F U hU μ H hH R p i-
        input G hG hβ ell hell hLower F U hU μ H hH R q i) (s,ω)‖^2) ∂SHE.PredictableL2.timeMeasure H) ≤
        UnboundedGlobalJointMoments.jointConstant (fun z => ‖G z‖) C β K H*
          ENNReal.ofReal (dist p q^UnboundedHeatIncrementCaps.exponent β) := by
  let vp := input G hG hβ ell hell hLower F U hU μ H hH R p i
  let vq := input G hG hβ ell hell hLower F U hU μ H hH R q i
  have he := fun r : HeatParameterCover.Parameter => MatrixPointHeatInput.input_ae F μ H hH
    (NativeMatrixEquation.cap (G_R R)) (NativeMatrixEquation.cap_nonneg (G_R R))
    (NativeMatrixEquation.profile F (G_R R) U hU) (fun _ => le_rfl)
    (NativeMatrixEquation.profile_measurable F (G_R R) U hU) (GlobalHeatParameter.time H r)
    (GlobalHeatParameter.time_le_horizon H r) (HeatParameterCoordinates.center r) i
  have hdiff : vp-vq=ᵐ[energyMeasure μ H] fun z =>
      MatrixPointHeatRows.row ((GlobalHeatParameter.time H p : ℝ)-(z.1 : ℝ))
        (NativeMatrixEquation.profile F (G_R R) U hU z) (HeatParameterCoordinates.center p) i-
      MatrixPointHeatRows.row ((GlobalHeatParameter.time H q : ℝ)-(z.1 : ℝ))
        (NativeMatrixEquation.profile F (G_R R) U hU z) (HeatParameterCoordinates.center q) i := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub vp vq),he p,he q] with z hs hp hq
    rw [hs]
    exact congrArg₂ HSub.hSub hp hq
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := SHE.PredictableL2.timeMeasure H)).quasiMeasurePreserving.ae hdiff
  filter_upwards [Measure.ae_ae_of_ae_prod hs,
    family_bracket G hG hβ hβ1 ell hell hLower F U hU μ H R p q i hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun s hs => congrArg (fun z => ENNReal.ofReal (‖z‖^2)) hs)).trans_le hb

include hβ1 in
/-- All dyadic even moments of the actual time-space point increments
are uniform over coefficient truncations after L2 history localization. -/
theorem native_moment (R : ℝ≥0) (p q : HeatParameterCover.Parameter) (i : Fin n) {K : ℝ}
    (hbound : ∀ᵐ z ∂energyMeasure μ H,‖U z‖≤K)
    (N : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode)) (k : ℕ) :
    (∫⁻ ω,ENNReal.ofReal (‖(FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (input G hG hβ ell hell hLower F U hU μ H hH R p i) ω-
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (input G hG hβ ell hell hLower F U hU μ H hH R q i) ω‖^(2*2^k)) ∂μ) ≤
        ((NativeScalarBDG.constant k : ℝ≥0∞)*UnboundedGlobalJointMoments.jointConstant
          (fun z => ‖G z‖) C β K H^(2^k))*edist p q^(UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) := by
  have hb := NativeScalarBDG.difference_moment_of_bracket_bound N MatrixPredictableHaarRotation.basis k _ _
    (input_bracket G hG hβ hβ1 ell hell hLower F U hU μ H hH R p q i hbound)
  refine hb.trans_eq ?_
  rw [←ENNReal.ofReal_rpow_of_nonneg dist_nonneg (UnboundedHeatIncrementCaps.exponent_pos hβ1).le,
    mul_pow,←ENNReal.rpow_mul_natCast,edist_dist]
  ring

end SHEStochastic.MatrixUnboundedPointIncrements
