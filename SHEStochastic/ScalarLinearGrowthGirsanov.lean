module

public import SHEStochastic.ScalarSignedControl
public import SHEStochastic.ScalarGirsanovCappedTransport
public import SHEStochastic.ScalarStoppedEquationTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLinearGrowthGirsanov
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

/-- The reverse change starts with drift present and shifts Brownian
motion by +b/g. The forward change uses the negative shift. -/
def present (reverse : Bool) : ℝ := if reverse then 1 else 0
def sign (reverse : Bool) : ℝ := if reverse then 1 else -1

theorem present_bound (reverse : Bool) : |present reverse|≤1 := by
  cases reverse <;> norm_num [present]

theorem sign_bound (reverse : Bool) : |sign reverse|≤1 := by
  cases reverse <;> norm_num [sign]

theorem switched (reverse : Bool) : present reverse-sign reverse=present (!reverse) := by
  cases reverse <;> norm_num [present,sign]

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ Noise)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (b : ScalarLinearGrowthDriftField.Data H) (c : ℝ≥0) (hc₀ : 0<c) (hg₀ : ∀ z,(c : ℝ)≤|g z|)
  (u₀ : RealL2)

local notation "bθ" => ScalarLinearGrowthDriftField.divideBy b g
  (Continuous.measurable (HolderWith.continuous hg hβ)) c hc₀ hg₀
local notation "θ" => ScalarDriftNativeDirection.row bθ (Function.uncurry W)
local notation "νin" m:max => FiniteScalarIto.inputMeasure F m H
local notation "J" m:max => FiniteCylindricalIto.terminalIto (FiniteScalarIto.Family.toCoordinates m) e
local notation "Q" => NativeGirsanovTilt.measure P e

/-- The actual linear-growth Girsanov change on the scalar stopped
Fourier mild equation, in both directions. The uncut energy estimate
is derived under every true capped tilt. -/
theorem change (hnull : NullCompleteFiltration.ContainsNullSets F μ) (reverse : Bool)
    (hEq : ScalarStoppedMildMoment.Equation F μ H W hW hc hg hβ hβ₁ (J P) b
      (fun _ _ => present reverse) u₀) :
    ∃ u : Lp Noise 2 (νin μ),u =ᵐ[νin μ] (fun p => sign reverse • θ p) ∧
      ∃ (_ : IsProbabilityMeasure (Q u)) (R : FiniteScalarIto.Family F (Q u) H ι),
        Q u ≪ μ ∧ μ ≪ Q u ∧
        ScalarStoppedMildMoment.Equation F (Q u) H W hW hc hg hβ hβ₁ (J R) b
          (fun _ _ => present (!reverse)) u₀ ∧
        ∀ (v : Lp Noise 2 (νin μ)) (w : Lp Noise 2 (νin (Q u))),v =ᵐ[νin μ] w →
          FiniteCylindricalIto.rawIntegral R.toCoordinates e w =ᵐ[Q u]
            (fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω+
              NativeCrossEnergy.cross v u ω) := by
  classical
  obtain ⟨M,hM,hMoment⟩ := ScalarStoppedMomentUniform.bound (H := H) hg hβ hβ₁ b u₀
  have hE₀ := hMoment F μ W hW hc (J P) _ hEq (fun _ => measurable_const) (fun _ _ => present_bound reverse)
  obtain ⟨u,hu,hEnergy⟩ := ScalarSignedControl.exists_signed F μ W hW bθ (sign reverse)
    (sign_bound reverse) (lt_of_le_of_lt hE₀ ENNReal.ofReal_lt_top)
  obtain ⟨A,hA,_,U,hU,hCap,hGood⟩ := ScalarNativeStoppedTilt.exists_stops e u
  let shift (k : ℕ) (t : ℝ≥0) (ω : Ω) := if A t ω<(k : ℝ) then sign reverse else 0
  have hShift (k : ℕ) : U k =ᵐ[νin μ] fun p => shift k p.1 p.2 • θ p := by
    filter_upwards [hU k,hu] with p hs hu
    rw [hs]
    by_cases h : A p.1 p.2<(k : ℝ)
    · rw [indicator_of_mem (show p∈{p | A p.1 p.2<(k : ℝ)} from h),hu]
      simp [shift,h]
    · rw [indicator_of_notMem (show p∉{p | A p.1 p.2<(k : ℝ)} from h)]
      simp [shift,h]
  have hSm (k : ℕ) (ω : Ω) : Measurable (fun t => shift k t ω) := by
    have hAm : Measurable (fun t => A t ω) :=
      (hA.mono (predictable_le_product F)).measurable.comp (measurable_id.prodMk measurable_const)
    exact Measurable.ite (measurableSet_lt hAm measurable_const) measurable_const measurable_const
  have hSb (k : ℕ) (t : ℝ≥0) (ω : Ω) : |shift k t ω|≤1 := by
    by_cases h : A t ω<(k : ℝ) <;> simp [shift,h,sign_bound]
  have hRes (k : ℕ) (t : ℝ≥0) (ω : Ω) : |present reverse-shift k t ω|≤1 := by
    by_cases h : A t ω<(k : ℝ)
    · simpa only [shift,ite_eq_left h,switched] using present_bound (!reverse)
    · simpa only [shift,ite_eq_right h,sub_zero] using present_bound reverse
  let K : ℝ≥0 := ⟨2*((bθ).growth : ℝ)^2*((H : ℝ)+M),by positivity⟩
  have hK (k : ℕ) : (∫⁻ ω,ENNReal.ofReal (NativeEnergy.energy u ω) ∂Q (U k))≤K := by
    obtain ⟨hQ,R,hQμ,hμQ,hI⟩ := ScalarGirsanovCappedTransport.change P e hnull (U k)
      (k : ℝ) (Nat.cast_nonneg _) (hCap k)
    have he := ScalarStoppedEquationTransport.transport F μ (Q (U k)) H P R e W hW hc hg hβ hβ₁
      b c hc₀ hg₀ u₀ hQμ hμQ (U k) (fun _ _ => present reverse) (shift k) (hShift k)
      (fun _ => measurable_const) (fun _ _ => present_bound reverse) (hSm k) (hSb k) hI hEq
    have hm := hMoment F (Q (U k)) W hW hc (J R) _ he
      (fun ω => measurable_const.sub (hSm k ω)) (hRes k)
    have hh := hEnergy (Q (U k)) hQμ M hM hm
    change _≤ENNReal.ofReal (K : ℝ) at hh
    rwa [ENNReal.ofReal_coe_nnreal] at hh
  obtain ⟨hQ,R,hQμ,hμQ,_,hI⟩ := ScalarGirsanovLocalization.change P e hnull u U hCap hGood K hK
  have hU := ScalarStoppedEquationTransport.transport F μ (Q u) H P R e W hW hc hg hβ hβ₁
    b c hc₀ hg₀ u₀ hQμ hμQ u (fun _ _ => present reverse) (fun _ _ => sign reverse) hu
    (fun _ => measurable_const) (fun _ _ => present_bound reverse)
    (fun _ => measurable_const) (fun _ _ => sign_bound reverse) hI hEq
  refine ⟨u,hu,hQ,R,hQμ,hμQ,?_,hI⟩
  simpa only [switched] using hU

end SHEStochastic.ScalarLinearGrowthGirsanov
