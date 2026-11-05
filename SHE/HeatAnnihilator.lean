module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic

/-! Actual polynomial differential annihilators for finite Gaussian spans.
The construction preserves all previously annihilated generators and has
order at most `2^q-1`, including arbitrary parameter collisions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatAnnihilator
open Polynomial

abbrev Parameter := ℂ × ℂ

def gaussian (p : Parameter) (z : ℂ) : ℂ := Complex.exp (-p.1 * z ^ 2 + p.2 * z)

def polynomialGaussian (p : Parameter) (P : ℂ[X]) (z : ℂ) : ℂ := P.eval z * gaussian p z

def firstOrder (p : Parameter) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv f z + (2 * p.1 * z - p.2) * f z

def stepPolynomial (base p : Parameter) (P : ℂ[X]) : ℂ[X] :=
  P.derivative + (C (2 * (p.1 - base.1)) * X + C (base.2 - p.2)) * P

theorem hasDerivAt_gaussian (p : Parameter) (z : ℂ) :
    HasDerivAt (gaussian p) ((-2 * p.1 * z + p.2) * gaussian p z) z := by
  have h := (((hasDerivAt_id z).pow 2).const_mul (-p.1)).add
    ((hasDerivAt_id z).const_mul p.2)
  convert! h.cexp using 1
  dsimp [gaussian]
  ring

theorem hasDerivAt_polynomialGaussian (p : Parameter) (P : ℂ[X]) (z : ℂ) :
    HasDerivAt (polynomialGaussian p P)
      (P.derivative.eval z * gaussian p z + P.eval z *
        ((-2 * p.1 * z + p.2) * gaussian p z)) z := by
  exact (P.hasDerivAt z).mul (hasDerivAt_gaussian p z)

/-- Applying one actual first-order differential factor transports only a
polynomial, and raises its degree by at most one. -/
theorem firstOrder_polynomialGaussian (base p : Parameter) (P : ℂ[X]) :
    firstOrder p (polynomialGaussian base P) = polynomialGaussian base (stepPolynomial base p P) := by
  funext z
  rw [firstOrder, (hasDerivAt_polynomialGaussian base P z).deriv]
  simp only [polynomialGaussian, stepPolynomial, eval_add, eval_mul, eval_C, eval_X]
  ring

theorem stepPolynomial_self (p : Parameter) (P : ℂ[X]) :
    stepPolynomial p p P = P.derivative := by simp [stepPolynomial]

theorem stepPolynomial_natDegree (base p : Parameter) (P : ℂ[X]) :
    (stepPolynomial base p P).natDegree ≤ P.natDegree + 1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_derivative_le P).trans (by omega)
  · have hl : (C (2 * (p.1 - base.1)) * X + C (base.2 - p.2)).natDegree ≤ 1 := by
      have hmul := natDegree_mul_le (p := (C (2 * (p.1 - base.1)) : ℂ[X])) (q := X)
      rw [natDegree_C, natDegree_X, zero_add] at hmul
      simpa only [natDegree_add_C] using hmul
    have hm := natDegree_mul_le (p := C (2 * (p.1 - base.1)) * X + C (base.2 - p.2)) (q := P)
    omega

def wordApply (word : List Parameter) (f : ℂ → ℂ) : ℂ → ℂ :=
  word.foldl (fun g p => firstOrder p g) f

def wordPolynomial (base : Parameter) (word : List Parameter) (P : ℂ[X]) : ℂ[X] :=
  word.foldl (fun Q p => stepPolynomial base p Q) P

theorem wordApply_polynomialGaussian (base : Parameter) (word : List Parameter) (P : ℂ[X]) :
    wordApply word (polynomialGaussian base P) = polynomialGaussian base (wordPolynomial base word P) := by
  induction word generalizing P with
  | nil => rfl
  | cons p word ih =>
    change wordApply word (firstOrder p (polynomialGaussian base P)) = _
    rw [firstOrder_polynomialGaussian, ih]
    rfl

theorem wordPolynomial_natDegree (base : Parameter) (word : List Parameter) (P : ℂ[X]) :
    (wordPolynomial base word P).natDegree ≤ P.natDegree + word.length := by
  induction word generalizing P with
  | nil => simp [wordPolynomial]
  | cons p word ih =>
    have h := ih (stepPolynomial base p P)
    have hs := stepPolynomial_natDegree base p P
    change (wordPolynomial base word (stepPolynomial base p P)).natDegree ≤ _
    simp only [List.length_cons]
    omega

theorem wordPolynomial_replicate (p : Parameter) (n : ℕ) (P : ℂ[X]) :
    wordPolynomial p (List.replicate n p) P = Polynomial.derivative^[n] P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, wordPolynomial, List.foldl_cons]
    change wordPolynomial p (List.replicate n p) (stepPolynomial p p P) = _
    rw [stepPolynomial_self, ih, Function.iterate_succ_apply]

theorem firstOrder_zero (p : Parameter) : firstOrder p 0 = 0 := by
  funext z
  simp [firstOrder]

theorem wordApply_zero (word : List Parameter) : wordApply word 0 = 0 := by
  induction word with
  | nil => rfl
  | cons p word ih => simpa only [wordApply, List.foldl_cons, firstOrder_zero] using ih

theorem wordApply_append (w v : List Parameter) (f : ℂ → ℂ) :
    wordApply (w ++ v) f = wordApply v (wordApply w f) := List.foldl_append

def annihilatorWord : List Parameter → List Parameter
  | [] => []
  | p :: ps => let w := annihilatorWord ps; w ++ List.replicate (w.length + 1) p

theorem annihilatorWord_length (ps : List Parameter) :
    (annihilatorWord ps).length + 1 = 2 ^ ps.length := by
  induction ps with
  | nil => simp [annihilatorWord]
  | cons p ps ih =>
    simp only [annihilatorWord, List.length_append, List.length_replicate, List.length_cons, pow_succ]
    omega

/-- Every generator of an arbitrary finite Gaussian span is annihilated by
one explicit actual differential word, including repeated generators. -/
theorem annihilatorWord_annihilates (ps : List Parameter) (p : Parameter) (hp : p ∈ ps) :
    wordApply (annihilatorWord ps) (gaussian p) = 0 := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rw [annihilatorWord, wordApply_append]
    rcases List.mem_cons.mp hp with rfl | hp
    · have hbase : gaussian p = polynomialGaussian p 1 := by funext z; simp [polynomialGaussian]
      rw [hbase, wordApply_polynomialGaussian, wordApply_polynomialGaussian,
        wordPolynomial_replicate]
      have hd := wordPolynomial_natDegree p (annihilatorWord ps) 1
      have hz : Polynomial.derivative^[(annihilatorWord ps).length + 1]
          (wordPolynomial p (annihilatorWord ps) 1) = 0 :=
        Polynomial.iterate_derivative_eq_zero (by simpa only [natDegree_one, zero_add] using Nat.lt_succ_of_le hd)
      rw [hz]
      funext z
      simp [polynomialGaussian]
    · rw [ih hp, wordApply_zero]

theorem firstOrder_finiteSum {ι : Type*} (I : Finset ι) (base : ι → Parameter)
    (P : ι → ℂ[X]) (c : ι → ℂ) (p : Parameter) :
    firstOrder p (fun z => ∑ i ∈ I, c i * polynomialGaussian (base i) (P i) z) =
      fun z => ∑ i ∈ I, c i * polynomialGaussian (base i) (stepPolynomial (base i) p (P i)) z := by
  funext z
  have hd := HasDerivAt.fun_sum (u := I) (fun i _ =>
    (hasDerivAt_polynomialGaussian (base i) (P i) z).const_mul (c i))
  rw [firstOrder, hd.deriv, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [polynomialGaussian, stepPolynomial, eval_add, eval_mul, eval_C, eval_X]
  ring

theorem wordApply_finiteSum {ι : Type*} (I : Finset ι) (base : ι → Parameter)
    (P : ι → ℂ[X]) (c : ι → ℂ) (word : List Parameter) :
    wordApply word (fun z => ∑ i ∈ I, c i * polynomialGaussian (base i) (P i) z) =
      fun z => ∑ i ∈ I, c i * polynomialGaussian (base i) (wordPolynomial (base i) word (P i)) z := by
  induction word generalizing P with
  | nil => rfl
  | cons p word ih =>
    change wordApply word (firstOrder p _) = _
    rw [firstOrder_finiteSum, ih]
    rfl

theorem annihilatorWord_finiteSum {ι : Type*} (I : Finset ι) (base : ι → Parameter)
    (c : ι → ℂ) (ps : List Parameter) (hmem : ∀ i ∈ I, base i ∈ ps) :
    wordApply (annihilatorWord ps) (fun z => ∑ i ∈ I, c i * gaussian (base i) z) = 0 := by
  have he : (fun z => ∑ i ∈ I, c i * gaussian (base i) z) =
      fun z => ∑ i ∈ I, c i * polynomialGaussian (base i) 1 z := by simp [polynomialGaussian]
  rw [he, wordApply_finiteSum]
  funext z
  apply Finset.sum_eq_zero
  intro i hi
  have h := congrFun (annihilatorWord_annihilates ps (base i) (hmem i hi)) z
  have hrep := congrFun (wordApply_polynomialGaussian (base i) (annihilatorWord ps) 1) z
  have hb : polynomialGaussian (base i) 1 = gaussian (base i) := by
    funext w
    simp [polynomialGaussian]
  rw [hb] at hrep
  rw [← hrep, h]
  simp

theorem annihilatorWord_mem (ps : List Parameter) (p : Parameter)
    (hp : p ∈ annihilatorWord ps) : p ∈ ps := by
  induction ps with
  | nil => simp [annihilatorWord] at hp
  | cons q ps ih =>
    rw [annihilatorWord, List.mem_append] at hp
    rcases hp with hp | hp
    · exact List.mem_cons_of_mem q (ih hp)
    · have he := List.eq_of_mem_replicate hp
      exact List.mem_cons.mpr (Or.inl he)

theorem annihilatorWord_span {n : ℕ} (base : Fin n → Parameter) (ps : List Parameter)
    (hmem : ∀ i, base i ∈ ps) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => gaussian (base i)))) :
    wordApply (annihilatorWord ps) f = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have he : f = fun z => ∑ i, c i * gaussian (base i) z := by
    rw [← hc]
    ext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact annihilatorWord_finiteSum Finset.univ base c ps (fun i _ => hmem i)

end SHE.HeatAnnihilator
