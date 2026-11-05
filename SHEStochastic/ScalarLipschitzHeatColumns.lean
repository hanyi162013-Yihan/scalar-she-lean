module

public import SHEStochastic.ScalarLipschitzHeatColumn
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzHeatColumns
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "w" => NativeFourierHeatCoordinate.weight
open ScalarLipschitzHeatColumn

theorem weighted_pair_energy (a : Noise) (n : ℤ) :
    ‖weighted a (w Complex.reCLM n)‖^2 + ‖weighted a (w Complex.imCLM n)‖^2 = ‖a‖^2 := by
  let A := weighted a (w Complex.reCLM n)
  let B := weighted a (w Complex.imCLM n)
  change ‖A‖^2 + ‖B‖^2 = _
  rw [realLp_norm_sq,realLp_norm_sq,realLp_norm_sq,←integral_add
    (Lp.memLp A).norm.integrable_sq (Lp.memLp B).norm.integrable_sq]
  apply integral_congr_ae
  filter_upwards [weighted_ae a (w Complex.reCLM n),weighted_ae a (w Complex.imCLM n)] with x ha hb
  change A x = _ at ha
  change B x = _ at hb
  simp only [ha,hb,Real.norm_eq_abs,sq_abs]
  have he : (w Complex.reCLM n x)^2+(w Complex.imCLM n x)^2=1 := by
    let z : ℂ := fourier (-n) x
    change (1*z.re)^2+(1*z.im)^2=1
    have hz : ‖z‖=1 := by simp [z,fourier_apply]
    have hs := Complex.sq_norm z
    rw [hz,Complex.normSq_apply] at hs
    nlinarith
  nlinarith [congrArg (fun t : ℝ => t*(a x)^2) he]

variable {I : Type*} (e : HilbertBasis I ℝ Noise)

/-- Parseval in both coordinates, for any square-summable Fourier multiplier
of the two signed noise rows. This also applies to an increment of the heat kernel. -/
theorem spectral_energy (a : Noise) (d : ℤ → ℝ) (hd : Summable (fun n => (d n)^2))
    (X : I → RealL2)
    (hX : ∀ i ψ n, φ ψ n (X i) = d n * inner ℝ (weighted a (w ψ n)) (e i)) :
    Summable (fun i => ‖X i‖^2) ∧
      (∑' i,‖X i‖^2) = (∑' n,(d n)^2)*‖a‖^2 := by
  let F : ℤ → I → ℝ := fun n i => (φ Complex.reCLM n (X i))^2 + (φ Complex.imCLM n (X i))^2
  have hrow (n : ℤ) : Summable (F n) ∧ (∑' i, F n i) = (d n)^2*‖a‖^2 := by
    have hr := HilbertTrace.basis_sq e (weighted a (w Complex.reCLM n))
    have hi := HilbertTrace.basis_sq e (weighted a (w Complex.imCLM n))
    have he (i : I) : F n i = (d n)^2 *
        (‖inner ℝ (e i) (weighted a (w Complex.reCLM n))‖^2 +
          ‖inner ℝ (e i) (weighted a (w Complex.imCLM n))‖^2) := by
      simp only [F,hX,real_inner_comm (e i),Real.norm_eq_abs,sq_abs]
      ring
    refine ⟨((hr.1.add hi.1).mul_left _).congr (fun i => (he i).symm),?_⟩
    simp_rw [he]
    rw [tsum_mul_left,hr.1.tsum_add hi.1,hr.2,hi.2,weighted_pair_energy]
  have hcol (i : I) : Summable (fun n => F n i) ∧ (∑' n, F n i) = ‖X i‖^2 :=
    ScalarHeatFourierEnergy.state_energy (X i)
  have hp : Summable (fun p : ℤ × I => F p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
    refine ⟨fun n => (hrow n).1,?_⟩
    exact (hd.mul_right (‖a‖^2)).congr (fun n => (hrow n).2.symm)
  have hp' : Summable (fun p : I × ℤ => F p.2 p.1) :=
    (Equiv.prodComm I ℤ).summable_iff.mpr hp
  have hci : Summable (fun i => ∑' n, F n i) :=
    ((summable_prod_of_nonneg (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))).mp hp').2
  refine ⟨hci.congr (fun i => (hcol i).2),?_⟩
  calc
    (∑' i,‖X i‖^2) = ∑' i, ∑' n, F n i := tsum_congr (fun i => (hcol i).2.symm)
    _ = ∑' p : I × ℤ, F p.2 p.1 := hp'.tsum_prod.symm
    _ = ∑' p : ℤ × I, F p.1 p.2 := (Equiv.prodComm I ℤ).tsum_eq (fun p : ℤ × I => F p.1 p.2)
    _ = ∑' n, ∑' i, F n i := hp.tsum_prod
    _ = (∑' n,(d n)^2)*‖a‖^2 := by simp only [fun n => (hrow n).2,tsum_mul_right]

theorem damp_summable {r : ℝ} (hr : 0<r) :
    Summable (fun n : ℤ => (Real.exp (-r*(n : ℝ)^2))^2) := by
  have he (n : ℤ) : (Real.exp (-r*(n : ℝ)^2))^2 = Real.exp (-(2*r)*(n : ℝ)^2) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  simpa only [he] using (ScalarHeatFourierEnergy.trace hr).1

theorem column_energy (r : ℝ) (a : Noise) :
    Summable (fun i => ‖column r a (e i)‖^2) := by
  by_cases hr : 0<r
  · exact (spectral_energy e a _ (damp_summable hr) _
      (fun i ψ n => column_mode hr a (e i) ψ n)).1
  · simp only [column_zero (le_of_not_gt hr),norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact summable_zero

/-- Actual Hilbert white-noise columns at age r. The kernel vanishes at
nonpositive ages. -/
def kernel (r : ℝ) (a : Noise) : HilbertColumns.Space I RealL2 :=
  HilbertColumns.ofSummable (fun i => column r a (e i)) (column_energy e r a)

theorem kernel_apply (r : ℝ) (a : Noise) (i : I) : kernel e r a i = column r a (e i) := rfl

theorem kernel_zero {r : ℝ} (hr : r≤0) (a : Noise) : kernel e r a = 0 := by
  apply lp.ext
  funext i
  exact column_zero hr a (e i)

theorem kernel_norm_sq {r : ℝ} (hr : 0<r) (a : Noise) :
    ‖kernel e r a‖^2 = (∑' n : ℤ,(Real.exp (-r*(n : ℝ)^2))^2)*‖a‖^2 := by
  rw [HilbertColumns.norm_sq]
  exact (spectral_energy e a _ (damp_summable hr) _
    (fun i ψ n => column_mode hr a (e i) ψ n)).2

end SHEStochastic.ScalarLipschitzHeatColumns
