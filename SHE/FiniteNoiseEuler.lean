module
public import SHE.CylindricalDriverLaw
public import Mathlib.MeasureTheory.Constructions.Pi
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.FiniteNoiseEuler
open Set MeasureTheory
open scoped NNReal
variable {E ι:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E][DecidableEq ι]
variable (H:ℝ≥0)(t:ℕ→Iic H)(heat:ℕ→E→L[ℝ] E)
variable (column:ℕ→E→ι→E)(F:Finset ι)(u₀:E)

/-- The finite-noise exponential Euler scheme is an explicit function
of the original driver coordinates. No solution law is an argument. -/
def state (B:ι×Iic H→ℝ):ℕ→E
  | 0=>u₀
  | k+1=>heat k (state B k)+
    ∑i∈F,(B (i,t (k+1))-B (i,t k)) • column k (state B k) i

theorem state_measurable (hcolumn:∀k i,Measurable (fun v=>column k v i))(n:ℕ):
    Measurable (fun B=>state H t heat column F u₀ B n):=by
  induction n with
  | zero=>exact measurable_const
  | succ k ih=>
    change Measurable (fun B=>heat k (state H t heat column F u₀ B k)+
      ∑i∈F,(B (i,t (k+1))-B (i,t k)) • column k (state H t heat column F u₀ B k) i)
    apply ((heat k).continuous.measurable.comp ih).add
    exact Finset.measurable_sum F (fun i _=>
      ((measurable_pi_apply (i,t (k+1))).sub (measurable_pi_apply (i,t k))).smul
        ((hcolumn k i).comp ih))

variable {Ω Ω':Type*}[MeasurableSpace Ω][MeasurableSpace Ω']

/-- Each actual finite-noise approximation is measurable in the
original past at its own time. Future driver coordinates are not used. -/
theorem state_adapted (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X:ι→ℝ≥0→Ω→ℝ)(hX:∀i,StronglyAdapted 𝓕 (X i))
    (ht:∀k,(t k).1≤(t (k+1)).1)
    (hcolumn:∀k i,Measurable (fun v=>column k v i))(n:ℕ):
    StronglyMeasurable[𝓕 (t n).1]
      (fun ω=>state H t heat column F u₀ (fun p=>X p.1 p.2.1 ω) n):=by
  induction n with
  | zero=>exact stronglyMeasurable_const
  | succ k ih=>
    have hs:=ih.mono (𝓕.mono (ht k))
    change StronglyMeasurable[𝓕 (t (k+1)).1] (fun ω=>
      heat k (state H t heat column F u₀ (fun p=>X p.1 p.2.1 ω) k)+
      ∑i∈F,(X i (t (k+1)).1 ω-X i (t k).1 ω) •
        column k (state H t heat column F u₀ (fun p=>X p.1 p.2.1 ω) k) i)
    apply ((heat k).continuous.comp_stronglyMeasurable hs).add
    have hh:=Finset.stronglyMeasurable_sum F (fun i _=>
      ((hX i (t (k+1)).1).sub ((hX i (t k).1).mono (𝓕.mono (ht k)))).smul
        (((hcolumn k i).comp hs.measurable).stronglyMeasurable))
    convert! hh using 1
    funext ω
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rfl

/-- Every finite-noise Euler state has the same law across original
probability spaces once the actual cylindrical Brownian laws agree.
Convergence to the SPDE solution is a separate obligation. -/
theorem law (μ:Measure Ω)(ν:Measure Ω')[IsFiniteMeasure μ][IsFiniteMeasure ν]
    (X:ι→ℝ≥0→Ω→ℝ)(Y:ι→ℝ≥0→Ω'→ℝ)
    (hX:∀i s,Measurable (X i s))(hY:∀i s,Measurable (Y i s))
    (hLX:CylindricalDriverLaw.Law μ H X)(hLY:CylindricalDriverLaw.Law ν H Y)
    (hcolumn:∀k i,Measurable (fun v=>column k v i))(n:ℕ):
    μ.map (fun ω=>state H t heat column F u₀ (fun p=>X p.1 p.2.1 ω) n)=
      ν.map (fun ω=>state H t heat column F u₀ (fun p=>Y p.1 p.2.1 ω) n):=by
  have hmX:Measurable (fun ω=>fun p:ι×Iic H=>X p.1 p.2.1 ω):=
    measurable_pi_iff.mpr (fun p=>hX _ _)
  have hmY:Measurable (fun ω=>fun p:ι×Iic H=>Y p.1 p.2.1 ω):=
    measurable_pi_iff.mpr (fun p=>hY _ _)
  have he:=congrArg (fun P:Measure (ι×Iic H→ℝ)=>P.map (fun B=>state H t heat column F u₀ B n))
    (CylindricalDriverLaw.map_eq μ ν H X Y hX hY hLX hLY)
  rw [Measure.map_map (state_measurable H t heat column F u₀ hcolumn n) hmX,
    Measure.map_map (state_measurable H t heat column F u₀ hcolumn n) hmY] at he
  exact he
end SHE.FiniteNoiseEuler
