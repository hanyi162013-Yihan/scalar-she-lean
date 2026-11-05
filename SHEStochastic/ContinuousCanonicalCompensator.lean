module

public import SHEStochastic.ContinuousPathIntegral
public import SHEStochastic.CanonicalFourierCompensator

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.ContinuousCanonicalCompensator
open MeasureTheory Filter SHE StoppedPathPasting AdaptedCanonicalPathTests PastedGeneratorFunctional
open scoped NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ι : Type*} [Countable ι] [DecidableEq ι] (H : ℝ≥0) (rate : ℝ) (hrate : 0≤rate)

def value (b : C(E,ℝ)) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) : ℝ :=
  ContinuousPathIntegral.value H (PathIntegratedCovariance.exponential H rate hrate) b x.1 (clock H t)

theorem continuous (b : C(E,ℝ)) (t : ℝ≥0) : Continuous (value (ι := ι) H rate hrate b t) :=
  (ContinuousPathIntegral.continuous H _ b).comp (continuous_fst.prodMk continuous_const)

/-- The existing bounded Fourier compensator is exactly this continuous
one when its state functional happens to be bounded. -/
theorem bounded_eq (b : BoundedContinuousFunction E ℝ) (t : ℝ≥0) :
    value (ι := ι) H rate hrate b.toContinuousMap t=
      CanonicalFourierCompensator.value H rate hrate b t := rfl

/-- The continuous compensator is the literal time integral of the
canonical state; boundedness of the state functional is unnecessary. -/
theorem canonical_value (b : C(E,ℝ)) (t : ℝ≥0)
    (x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    value H rate hrate b t x = ∫ s in (0 : ℝ)..(min t H : ℝ≥0),
      Real.exp (s*rate)*b (CanonicalStateDriverFiltration.state H s.toNNReal x) := by
  apply intervalIntegral.integral_congr_Ioo_of_le (clock H t).property.1
  intro s hs
  have hsH : s∈Set.Icc (0 : ℝ) (H : ℝ) :=
    ⟨hs.1.le,hs.2.le.trans (clock H t).property.2⟩
  change PathIntegratedCovariance.exponential H rate hrate s*b (read H x.1 s)=_
  rw [PathIntegratedCovariance.exponential_apply H rate hrate s hsH]
  congr 1
  change b (read H x.1 s)=b (x.1 (CanonicalStateDriverFiltration.clock H s.toNNReal))
  rw [show read H x.1 s=x.1 (⟨s,hsH⟩ : Time H) from read_val H x.1 ⟨s,hsH⟩]
  congr 2
  apply Subtype.ext
  change s=min (s.toNNReal : ℝ) (H : ℝ)
  rw [Real.coe_toNNReal s hsH.1,min_eq_left hsH.2]

/-- Compact-uniform convergence of the literal state compensators
passes to the actual joint state/noise path space. -/
theorem uniformly_on_compact (bn : ℕ → C(E,ℝ)) (b : C(E,ℝ))
    (hb : ∀ s : Set E,IsCompact s → TendstoUniformlyOn (fun m => bn m) b atTop s)
    {K : Set (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H)} (hK : IsCompact K) (t : ℝ≥0) :
    TendstoUniformlyOn (fun m => value H rate hrate (bn m) t) (value H rate hrate b t) atTop K := by
  have hh := ContinuousPathIntegral.uniformly_on_compact H
    (PathIntegratedCovariance.exponential H rate hrate) bn b hb (hK.image continuous_fst)
  have hc := (hh.comp (fun x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H =>
    (x.1,clock H t))).mono (show K⊆_ from fun x hx => ⟨⟨x,hx,rfl⟩,Set.mem_univ _⟩)
  simpa only [TendstoUniformlyOn,value,Function.comp_def] using hc

/-- These unbounded continuous compensators are measurable in the
actual canonical past filtration; no global value bound is needed. -/
theorem adapted (b : C(E,ℝ)) : StronglyAdapted (CanonicalStateDriverFiltration.filtration H)
    (value (ι := ι) H rate hrate b) := by
  intro t
  let F := CanonicalStateDriverFiltration.filtration (E := E) (ι := ι) H
  let w := PathIntegratedCovariance.exponential H rate hrate
  let test : C(Path H E,ℝ) :=
    ⟨fun p => ContinuousPathIntegral.value H w b p (clock H t),
      (ContinuousPathIntegral.continuous H w b).comp (continuous_id.prodMk continuous_const)⟩
  have hp (q : Time H) : Measurable[F (toNN H q)]
      (fun x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H => x.1 q) :=
    (JointCanonicalCylinderRecognition.adapted H q).fst
  have htest : PastedPastTests.UsesPast H (clock H t) test := by
    intro x y hxy
    apply intervalIntegral.integral_congr_Ioo_of_le (clock H t).property.1
    intro s hs
    have hsH : s∈Set.Icc (0 : ℝ) (H : ℝ) := ⟨hs.1.le,hs.2.le.trans (clock H t).property.2⟩
    change w s*b (read H x (⟨s,hsH⟩ : Time H).val)=w s*b (read H y (⟨s,hsH⟩ : Time H).val)
    rw [read_val,read_val,hxy ⟨s,hsH⟩ hs.2.le]
  exact (continuous_past_test_measurable H F Prod.fst hp (clock H t) test htest).mono
    (F.mono (show toNN H (clock H t)≤t from min_le_left _ _))

end SHEStochastic.ContinuousCanonicalCompensator
