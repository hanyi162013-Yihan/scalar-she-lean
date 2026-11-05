module

public import SHEStochastic.PastedHeatProductFunctional
public import SHEStochastic.PastedLinearHeatMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.PastedHeatProductMartingale
open MeasureTheory ProbabilityTheory StoppedPathPasting PastedPastTests
open scoped NNReal

variable {E Ω : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  (H : ℝ≥0) (ell₁ ell₂ : E →L[ℝ] ℝ) (lam₁ lam₂ : ℝ)
  (hRate : 0 ≤ lam₁+lam₂) (b : BoundedContinuousFunction E ℝ)

local notation "M₁" => PastedLinearHeatFunctional.value H ell₁ lam₁
local notation "M₂" => PastedLinearHeatFunctional.value H ell₂ lam₂
local notation "V" => PastedHeatProductFunctional.value H ell₁ ell₂ lam₁ lam₂ hRate b

def Identity (ν : Measure (Path H E)) : Prop :=
  ∀ s t : Time H, s.val ≤ t.val →
    ∀ test : BoundedContinuousFunction (Path H E) ℝ, UsesPast H s test →
      (∫ x, test x*(V x t-V x s) ∂ν) = 0

variable (X : Ω → Path H E) (exit : Ω → Time H)

def prefixPart (s t : Time H) (ω : Ω) : ℝ :=
  V (X ω) (pastTime H (exit ω) t)-V (X ω) (pastTime H (exit ω) s)

def productPart (s t : Time H) (z : Ω × Path H E) : ℝ :=
  Real.exp ((lam₁+lam₂)*(exit z.1).val)*
    (V z.2 (futureTime H (exit z.1) t)-V z.2 (futureTime H (exit z.1) s))

def crossPart (s t : Time H) (z : Ω × Path H E) : ℝ :=
  (M₁ (X z.1) (exit z.1)*Real.exp (lam₂*(exit z.1).val))*
    (M₂ z.2 (futureTime H (exit z.1) t)-M₂ z.2 (futureTime H (exit z.1) s))

variable (hX : Measurable X) (hr : Measurable exit)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Kernel E (Path H E)) [IsMarkovKernel κ]

local notation "ν" => StoppedContinuationMeasure.joint H X exit hX hr μ κ

include hX in
theorem source_identity (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hadapt : ∀ t : Time H, Measurable[F (AdaptedCanonicalPathTests.toNN H t)] (fun ω ↦ X ω t))
    (hM : Martingale (fun q ω ↦ V (X ω) (AdaptedCanonicalPathTests.clock H q)) F μ) :
    Identity H ell₁ ell₂ lam₁ lam₂ hRate b (μ.map X) := by
  intro s t hst test htest
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hM
    (AdaptedCanonicalPathTests.toNN H s) (AdaptedCanonicalPathTests.toNN H t) hst
    (fun ω ↦ test (X ω))
    (AdaptedCanonicalPathTests.past_test_measurable H F X hadapt s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  simp only [AdaptedCanonicalPathTests.clock_toNN] at hh
  have hv (q : Time H) : Continuous (fun x : Path H E ↦ V x q) :=
    (PastedHeatProductFunctional.continuous_value H ell₁ ell₂ lam₁ lam₂ hRate b).comp
      (continuous_id.prodMk continuous_const)
  exact (integral_map_of_stronglyMeasurable hX
    (test.continuous.mul ((hv t).sub (hv s))).stronglyMeasurable).trans hh

theorem stopped_source_identity (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hadapt : ∀ t : Time H, Measurable[F (AdaptedCanonicalPathTests.toNN H t)] (fun ω ↦ X ω t))
    (hM : Martingale (fun q ω ↦ V (X ω)
      (pastTime H (exit ω) (AdaptedCanonicalPathTests.clock H q))) F μ)
    (s t : Time H) (hst : s.val ≤ t.val) (test : BoundedContinuousFunction (Path H E) ℝ)
    (htest : UsesPast H s test) :
    (∫ ω, test (X ω)*prefixPart H ell₁ ell₂ lam₁ lam₂ hRate b X exit s t ω ∂μ) = 0 := by
  have hh := ContinuousStoppedMartingaleTests.weighted_increment μ F _ hM
    (AdaptedCanonicalPathTests.toNN H s) (AdaptedCanonicalPathTests.toNN H t) hst
    (fun ω ↦ test (X ω))
    (AdaptedCanonicalPathTests.past_test_measurable H F X hadapt s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  simpa only [prefixPart, AdaptedCanonicalPathTests.clock_toNN] using hh

/-- One Fubini proof handles both the square and the mixed driver
compensator. Each random join cross term is retained explicitly. -/
theorem joint_identity
    (hinitial : ∀ᵐ ω ∂μ, ∀ᵐ y ∂κ (StoppedContinuationMeasure.state H X exit ω),
      y (origin H) = StoppedContinuationMeasure.state H X exit ω)
    (hProduct : ∀ᵐ ω ∂μ, Identity H ell₁ ell₂ lam₁ lam₂ hRate b
      (κ (StoppedContinuationMeasure.state H X exit ω)))
    (hModes : ∀ᵐ ω ∂μ,
      PastedLinearHeatMartingale.Identity H ell₁ lam₁ (κ (StoppedContinuationMeasure.state H X exit ω)) ∧
      PastedLinearHeatMartingale.Identity H ell₂ lam₂ (κ (StoppedContinuationMeasure.state H X exit ω)))
    (s t : Time H) (hst : s.val ≤ t.val) (test : BoundedContinuousFunction (Path H E) ℝ)
    (htest : UsesPast H s test)
    (hipre : Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      prefixPart H ell₁ ell₂ lam₁ lam₂ hRate b X exit s t z.1) ν)
    (hi₀ : Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      productPart H ell₁ ell₂ lam₁ lam₂ hRate b exit s t z) ν)
    (hi₁ : Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      crossPart H ell₁ ell₂ lam₁ lam₂ X exit s t z) ν)
    (hi₂ : Integrable (fun z ↦ test (StoppedContinuationMeasure.value H X exit z)*
      crossPart H ell₂ ell₁ lam₂ lam₁ X exit s t z) ν)
    (horiginal : (∫ ω, test (X ω)*prefixPart H ell₁ ell₂ lam₁ lam₂ hRate b X exit s t ω ∂μ) = 0) :
    (∫ z, test (StoppedContinuationMeasure.value H X exit z)*
      (V (StoppedContinuationMeasure.value H X exit z) t-
        V (StoppedContinuationMeasure.value H X exit z) s) ∂ν) = 0 := by
  let K := StoppedContinuationMeasure.continuation H X exit hX hr κ
  let T := fun z : Ω × Path H E ↦ test (StoppedContinuationMeasure.value H X exit z)
  let pre := prefixPart H ell₁ ell₂ lam₁ lam₂ hRate b X exit s t
  let p₀ := productPart H ell₁ ell₂ lam₁ lam₂ hRate b exit s t
  let p₁ := crossPart H ell₁ ell₂ lam₁ lam₂ X exit s t
  let p₂ := crossPart H ell₂ ell₁ lam₂ lam₁ X exit s t
  let post := fun z ↦ (p₀ z+p₁ z)+p₂ z
  apply KernelMartingalePasting.cylinder_identity_of_split μ K _ T post pre (fun ω ↦ test (X ω))
  · filter_upwards [StoppedContinuationMeasure.matching_initial_of_ae H X exit hX hr μ κ hinitial] with z hz
    have hh := PastedHeatProductFunctional.increment_paste H ell₁ ell₂ lam₁ lam₂ hRate b
      (exit z.1) s t (X z.1) z.2 hz
    simpa only [StoppedContinuationMeasure.value, pre, post, p₀, p₁, p₂,
      prefixPart, productPart, crossPart, add_assoc] using hh
  · intro z hz
    exact PastedHeatProductFunctional.test_of_pre_nonzero H ell₁ ell₂ lam₁ lam₂ hRate b
      s t (exit z.1) hst test htest (X z.1) z.2 hz
  · exact hipre
  · convert (hi₀.add hi₁).add hi₂ using 1
    · funext z
      change T z*((p₀ z+p₁ z)+p₂ z) = (T z*p₀ z+T z*p₁ z)+T z*p₂ z
      ring
    · rfl
  · exact horiginal
  · filter_upwards [hProduct, hModes, hi₀.ae_of_compProd, hi₁.ae_of_compProd, hi₂.ae_of_compProd]
      with ω hp hm hi0 hi1 hi2
    let ψ := test.compContinuous ⟨fun y ↦ paste H (exit ω) (X ω) y,
      (continuous_paste H).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))⟩
    have hshift := shifted_test H s (exit ω) test htest (X ω)
    have hst' : (futureTime H (exit ω) s).val ≤ (futureTime H (exit ω) t).val :=
      max_le_max_right _ (sub_le_sub_right hst _)
    have scale (c : ℝ) (d : Path H E → ℝ) (hd : (∫ y, ψ y*d y ∂K ω) = 0) :
        (∫ y, T (ω,y)*(c*d y) ∂K ω) = 0 := by
      have he (y : Path H E) : T (ω,y)*(c*d y) = c*(ψ y*d y) := by
        change ψ y*(c*d y) = c*(ψ y*d y)
        ring
      simp_rw [he]
      rw [integral_const_mul, hd, mul_zero]
    have hz0 : (∫ y, T (ω,y)*p₀ (ω,y) ∂K ω) = 0 :=
      scale (Real.exp ((lam₁+lam₂)*(exit ω).val)) _ (hp _ _ hst' ψ hshift)
    have hz1 : (∫ y, T (ω,y)*p₁ (ω,y) ∂K ω) = 0 :=
      scale (M₁ (X ω) (exit ω)*Real.exp (lam₂*(exit ω).val)) _ (hm.2 _ _ hst' ψ hshift)
    have hz2 : (∫ y, T (ω,y)*p₂ (ω,y) ∂K ω) = 0 :=
      scale (M₂ (X ω) (exit ω)*Real.exp (lam₁*(exit ω).val)) _ (hm.1 _ _ hst' ψ hshift)
    have he (y : Path H E) : T (ω,y)*post (ω,y) =
        (T (ω,y)*p₀ (ω,y)+T (ω,y)*p₁ (ω,y))+T (ω,y)*p₂ (ω,y) := by dsimp only [post]; ring
    simp_rw [he]
    calc
      _ = (∫ y, T (ω,y)*p₀ (ω,y)+T (ω,y)*p₁ (ω,y) ∂K ω)+
          ∫ y, T (ω,y)*p₂ (ω,y) ∂K ω := integral_add (hi0.add hi1) hi2
      _ = ((∫ y, T (ω,y)*p₀ (ω,y) ∂K ω)+∫ y, T (ω,y)*p₁ (ω,y) ∂K ω)+
          ∫ y, T (ω,y)*p₂ (ω,y) ∂K ω := by
        congr 1
        exact integral_add hi0 hi1
      _ = 0 := by rw [hz0, hz1, hz2]; simp

section Recognition
variable [TopologicalSpace.MetrizableSpace (Path H E)]

/-- Product past-test identities identify the actual martingale in the
full path filtration, using the existing L2 density theorem. -/
theorem martingale (ρ : Measure (Path H E)) [IsProbabilityMeasure ρ]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Path H E)))
    (hadapt : ∀ t : Time H, Measurable[F (AdaptedCanonicalPathTests.toNN H t)] (fun x : Path H E ↦ x t))
    (hF : ∀ q, F q ≤ MeasurableSpace.comap (stopped H (AdaptedCanonicalPathTests.clock H q)) inferInstance)
    (hId : Identity H ell₁ ell₂ lam₁ lam₂ hRate b ρ)
    (hMom : ∀ q, MemLp (fun x ↦ V x (AdaptedCanonicalPathTests.clock H q)) 2 ρ) :
    Martingale (fun q x ↦ V x (AdaptedCanonicalPathTests.clock H q)) F ρ := by
  letI : MetricSpace (Path H E) := TopologicalSpace.metrizableSpaceMetric _
  have he (t : Time H) (x : Path H E) : V (stopped H t x) t = V x t := by
    apply PastedHeatProductFunctional.usesPast H ell₁ ell₂ lam₁ lam₂ hRate b t
    intro q hq
    change x (pastTime H t q) = x q
    congr 1
    exact Subtype.ext (min_eq_left hq)
  have ha : StronglyAdapted F (fun q x ↦ V x (AdaptedCanonicalPathTests.clock H q)) := by
    intro q
    have hstop := (AdaptedCanonicalPathTests.measurable_stopped H F id hadapt
      (AdaptedCanonicalPathTests.clock H q)).mono
        (F.mono (show AdaptedCanonicalPathTests.toNN H (AdaptedCanonicalPathTests.clock H q) ≤ q from min_le_left _ _)) le_rfl
    have hv : Continuous (fun x : Path H E ↦ V x (AdaptedCanonicalPathTests.clock H q)) :=
      (PastedHeatProductFunctional.continuous_value H ell₁ ell₂ lam₁ lam₂ hRate b).comp
        (continuous_id.prodMk continuous_const)
    have hh : StronglyMeasurable[F q] (fun x : Path H E ↦
        V (stopped H (AdaptedCanonicalPathTests.clock H q) x) (AdaptedCanonicalPathTests.clock H q)) :=
      (hv.measurable.comp hstop).stronglyMeasurable
    simpa only [he] using hh
  apply BCFPastTesting.martingale ρ (F := F)
    (past := fun q ↦ stopped H (AdaptedCanonicalPathTests.clock H q))
    (fun q ↦ (continuous_stopped H).measurable.comp (measurable_const.prodMk measurable_id)) hF _ ha hMom
  intro s t hst f
  let ψ := f.compContinuous ⟨stopped H (AdaptedCanonicalPathTests.clock H s),
    (continuous_stopped H).comp (continuous_const.prodMk continuous_id)⟩
  apply hId (AdaptedCanonicalPathTests.clock H s) (AdaptedCanonicalPathTests.clock H t)
    (min_le_min_right _ (by exact_mod_cast hst)) ψ
  intro x y hxy
  apply congrArg f
  apply ContinuousMap.ext
  intro q
  exact hxy (pastTime H (AdaptedCanonicalPathTests.clock H s) q) (min_le_right _ _)

end Recognition
end SHEStochastic.PastedHeatProductMartingale
