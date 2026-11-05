module

public import SHE.FiniteItoNoise

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Accepted stochastic package 2 in universal form: the ordinary
finite-dimensional Itô formula for an arbitrary finite family of scalar
integrals. Package 1 supplies the ordinary integrals and their common
noise; all heat-specific rows and brackets are outside this interface. -/
noncomputable section
namespace SHE.StandardFiniteIto
open MeasureTheory Set PredictableL2 GaussianItoTest StoppedItoInputs FiniteItoNoise
open scoped NNReal ENNReal
abbrev State (n : ℕ) := WordRecursion.State n
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (h : ℝ≥0)

def vectorIntegral (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) {n : ℕ}
    (z : State n) (R : Fin n → Process (E := C) 𝓕 μ h) (t : ℝ≥0) (ω : Ω) : State n :=
  WithLp.toLp 2 (fun i => z i+J.integral (stop 𝓕 μ h t (R i)) ω)

def rowCovariance {n : ℕ} (R : Fin n → Process (E := C) 𝓕 μ h)
    (ω : Ω) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ (R i (t.toNNReal,ω)) (R j (t.toNNReal,ω))

/-- The usual finite-dimensional Itô formula, universally quantified over
all predictable L² noise rows, continuous versions of their integrals,
and regular deterministic tests. The martingale term is the actual
gradient-row scalar Itô integral constructed in FiniteItoNoise. -/
structure Universal (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h) : Prop where
  formula : ∀ {n : ℕ} (R : Fin n → Process (E := C) 𝓕 μ h) (z : State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[𝓕.predictable] Y),
    (∀ ω,Continuous (fun t => Y (t,ω))) →
    (∀ (t : ℝ≥0),t ≤ h → (fun ω => Y (t,ω))=ᵐ[μ] vectorIntegral 𝓕 μ h J z R t) →
    ∀ {a b : ℝ},0 ≤ a → a ≤ b → b ≤ (h:ℝ) →
    ∀ (G dG : ℝ → State n → ℝ),RegularTest a b G dG → ∀ᵐ ω ∂μ,
      G b (Y (b.toNNReal,ω))=G a (Y (a.toNNReal,ω))+
        noise 𝓕 μ h Y hY R J a b G ω+
        ∫ t in a..b,dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
          GaussianTaylorAverage.covarianceAction (rowCovariance 𝓕 μ h R ω t)
            (GaussianTaylor.hessian (G t) (Y (t.toNNReal,ω)))

/-- Applying the ordinary formula leaves precisely the generic Itô
input expected by the deterministic Gaussian backward calculation. -/
theorem finiteItoInput (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (hJ : Universal 𝓕 μ h J) {n : ℕ}
    (R : Fin n → Process (E := C) 𝓕 μ h) (z : State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[𝓕.predictable] Y)
    (hc : ∀ ω,Continuous (fun t => Y (t,ω)))
    (hRep : ∀ (t : ℝ≥0),t ≤ h → (fun ω => Y (t,ω))=ᵐ[μ] vectorIntegral 𝓕 μ h J z R t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (h:ℝ)) :
    PhysicalIto.FiniteItoInput μ (fun ω t => Y (t.toNNReal,ω))
      (rowCovariance 𝓕 μ h R) a b
      (fun G ω => noise 𝓕 μ h Y hY R J a b G ω) := by
  intro G dG hG
  exact hJ.formula R z Y hY hc hRep ha hab hb G dG hG

end SHE.StandardFiniteIto
